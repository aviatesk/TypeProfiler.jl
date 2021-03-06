@testset "cache per configuration" begin
    # cache key should be same for the same configurations
    let
        k1 = JET.get_cache_key(JETAnalyzer())

        k2 = JET.get_cache_key(JETAnalyzer())

        @test k1 == k2
    end

    # cache key should be different for different configurations
    let
        interp1 = JETAnalyzer(; max_methods=3)
        k1 = JET.get_cache_key(interp1)

        interp2 = JETAnalyzer(; max_methods=4)
        k2 = JET.get_cache_key(interp2)

        @test k1 ≠ k2
    end

    # configurations other than `JETAnalysisParams`, `InferenceParams` and `ReportPass`
    # shouldn't affect the cache key identity
    let
        interp1 = JETAnalyzer(; toplevel_logger=nothing)
        k1 = JET.get_cache_key(interp1)

        interp2 = JETAnalyzer(; toplevel_logger=IOBuffer())
        k2 = JET.get_cache_key(interp2)

        @test k1 == k2
    end

    # cache key should be different for different report passes
    let
        interp1 = JETAnalyzer(; report_pass=JET.BasicPass())
        k1 = JET.get_cache_key(interp1)

        interp2 = JETAnalyzer(; report_pass=JET.SoundPass())
        k2 = JET.get_cache_key(interp2)

        @test k1 ≠ k2
    end

    # end to end test
    let
        m = Module()
        @eval m begin
            foo(a::Val{1}) = 1
            foo(a::Val{2}) = 2
            foo(a::Val{3}) = 3
            foo(a::Val{4}) = undefvar
        end

        # run first analysis and cache
        analyzer, frame = @eval m $analyze_call((Int,); max_methods=3) do a
            foo(Val(a))
        end
        @test isempty(get_reports(analyzer))

        # should use the cached result
        analyzer, frame = @eval m $analyze_call((Int,); max_methods=3) do a
            foo(Val(a))
        end
        @test isempty(get_reports(analyzer))

        # should re-run analysis, and should get a report
        analyzer, frame = @eval m $analyze_call((Int,); max_methods=4) do a
            foo(Val(a))
        end
        @test any(get_reports(analyzer)) do r
            isa(r, GlobalUndefVarErrorReport) &&
            r.name === :undefvar
        end

        # should run the cached previous result
        analyzer, frame = @eval m $analyze_call((Int,); max_methods=4) do a
            foo(Val(a))
        end
        @test any(get_reports(analyzer)) do r
            isa(r, GlobalUndefVarErrorReport) &&
            r.name === :undefvar
        end
    end
end

@testset "invalidate native code cache" begin
    # invalidate native code cache in a system image if it has not been analyzed by JET
    # yes this slows down anlaysis for sure, but otherwise JET will miss obvious errors like below
    let
        analyzer, frame = analyze_call((Nothing,)) do a
            a.field
        end
        @test length(get_reports(analyzer)) === 1
    end

    # invalidation from deeper call site can refresh JET analysis
    let
        # NOTE: branching on https://github.com/JuliaLang/julia/pull/38830
        symarg = last(first(methods(Base.show_sym)).sig.parameters) === Symbol ?
                 :(sym::Symbol) :
                 :(sym)

        l1, l2, l3 = @freshexec begin
            # ensure we start with this "errorneous" `show_sym`
            @eval Base begin
                function show_sym(io::IO, $(symarg); allow_macroname=false)
                    if is_valid_identifier(sym)
                        print(io, sym)
                    elseif allow_macroname && (sym_str = string(sym); startswith(sym_str, '@'))
                        print(io, '@')
                        show_sym(io, sym_str[2:end]) # NOTE: `sym_str[2:end]` here is errorneous
                    else
                        print(io, "var", repr(string(sym)))
                    end
                end
            end

            # should have error reported
            interp1, = @analyze_call println(QuoteNode(nothing))

            # should invoke invalidation in the deeper call site of `println(::QuoteNode)`
            @eval Base begin
                function show_sym(io::IO, $(symarg); allow_macroname=false)
                    if is_valid_identifier(sym)
                        print(io, sym)
                    elseif allow_macroname && (sym_str = string(sym); startswith(sym_str, '@'))
                        print(io, '@')
                        show_sym(io, Symbol(sym_str[2:end]))
                    else
                        print(io, "var", repr(string(sym)))
                    end
                end
            end

            # now we shouldn't have reports
            interp2, = @analyze_call println(QuoteNode(nothing))

            # again, invoke invalidation
            @eval Base begin
                function show_sym(io::IO, $(symarg); allow_macroname=false)
                    if is_valid_identifier(sym)
                        print(io, sym)
                    elseif allow_macroname && (sym_str = string(sym); startswith(sym_str, '@'))
                        print(io, '@')
                        show_sym(io, sym_str[2:end])
                    else
                        print(io, "var", repr(string(sym)))
                    end
                end
            end

            # now we should have reports, again
            interp3, = @analyze_call println(QuoteNode(nothing))

            (length ∘ JET.get_reports).((interp1, interp2, interp3)) # return
        end

        @test l1 > 0
        @test l2 == 0
        @test l3 == l1
    end
end

@testset "integrate with global code cache" begin
    # analysis for `sum(::String)` is already cached, `sum′` and `sum′′` should use it
    let
        m = gen_virtual_module()
        analyzer, frame = Core.eval(m, quote
            sum′(s) = sum(s)
            sum′′(s) = sum′(s)
            $analyze_call() do
                sum′′("julia")
            end
        end)
        test_sum_over_string(analyzer)
    end

    # incremental setup
    let
        m = gen_virtual_module()

        analyzer, frame = Core.eval(m, quote
            $analyze_call() do
                sum("julia")
            end
        end)
        test_sum_over_string(analyzer)

        analyzer, frame = Core.eval(m, quote
            sum′(s) = sum(s)
            $analyze_call() do
                sum′("julia")
            end
        end)
        test_sum_over_string(analyzer)

        analyzer, frame = Core.eval(m, quote
            sum′′(s) = sum′(s)
            $analyze_call() do
                sum′′("julia")
            end
        end)
        test_sum_over_string(analyzer)
    end

    # should not error for virtual stacktrace traversing with a frame for inner constructor
    # https://github.com/aviatesk/JET.jl/pull/69
    let
        res = @analyze_toplevel begin
            struct Foo end
            println(Foo())
        end
        @test isempty(res.inference_error_reports)
    end
end

@testset "integrate with local code cache" begin
    let
        m = gen_virtual_module()
        analyzer, frame = Core.eval(m, quote
            struct Foo{T}
                bar::T
            end
            $analyze_call((Foo{Int},)) do foo
                foo.baz # typo
            end
        end)

        @test !isempty(get_reports(analyzer))
        @test !isempty(get_cache(analyzer))
        @test any(get_cache(analyzer)) do analysis_result
            analysis_result.argtypes==Any[CC.Const(getproperty),m.Foo{Int},CC.Const(:baz)]
        end
    end

    let
        m = gen_virtual_module()
        analyzer, frame = Core.eval(m, quote
            struct Foo{T}
                bar::T
            end
            getter(foo, prop) = getproperty(foo, prop)
            $analyze_call((Foo{Int}, Bool)) do foo, cond
                getter(foo, :bar)
                cond ? getter(foo, :baz) : getter(foo, :qux) # non-deterministic typos
            end
        end)

        # there should be local cache for each errorneous constant analysis
        @test !isempty(get_reports(analyzer))
        @test !isempty(get_cache(analyzer))
        @test any(get_cache(analyzer)) do analysis_result
            analysis_result.argtypes==Any[CC.Const(m.getter),m.Foo{Int},CC.Const(:baz)]
        end
        @test any(get_cache(analyzer)) do analysis_result
            analysis_result.argtypes==Any[CC.Const(m.getter),m.Foo{Int},CC.Const(:qux)]
        end
    end
end
