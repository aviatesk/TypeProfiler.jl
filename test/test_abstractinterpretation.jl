@testset "report no method matching" begin
    # if there is no method matching case, it should be reported
    let
        # NOTE: we can't just wrap them into `let`, closures can't be inferred correctly
        m = gen_virtual_module()
        interp, frame = Core.eval(m, quote
            foo(a::Integer) = :Integer
            $analyze_call((AbstractString,)) do a
                foo(a)
            end
        end)
        @test length(interp.reports) === 1
        report = first(interp.reports)
        @test report isa NoMethodErrorReport
        @test report.t === Tuple{typeof(m.foo), AbstractString}
    end

    # we want to get report on `zero(Any)` for this case, but `Any`-typed statement can't
    # propagate to the error points ...
    let
        interp, report = analyze_call(()->sum([]))
        @test_broken !isempty(interp.reports)
    end

    # if there is no method matching case in union-split, it should be reported
    let
        m = gen_virtual_module()
        interp, frame = Core.eval(m, quote
            foo(a::Integer) = :Integer
            foo(a::AbstractString) = "AbstractString"

            $analyze_call(a->foo(a), (Union{Nothing,Int},))
        end)

        @test length(interp.reports) === 1
        report = first(interp.reports)
        @test report isa NoMethodErrorReport
        @test report.t == [Tuple{typeof(m.foo), Nothing}]
    end
end

@testset "report local undefined variables" begin
    let
        interp, frame = analyze_call((Bool,)) do b
            if b
                bar = rand(Int)
                return bar
            end
            return bar # undefined in this pass
        end
        @test length(interp.reports) === 1
        r = first(interp.reports)
        @test r isa LocalUndefVarErrorReport
        @test r.name === :bar
        @test last(r.vst).line == (@__LINE__)-6
    end

    # deeper level
    let
        m = @fixturedef begin
            function foo(b)
                if b
                    bar = rand(Int)
                    return bar
                end
                return bar # undefined in this pass
            end
            baz(a) = foo(a)
        end

        interp, frame = Core.eval(m, :($analyze_call(baz, (Bool,))))
        @test length(interp.reports) === 1
        r = first(interp.reports)
        @test r isa LocalUndefVarErrorReport
        @test r.name === :bar
        @test last(r.vst).line == (@__LINE__)-10

        # works when cached
        interp, frame = Core.eval(m, :($analyze_call(baz, (Bool,))))
        @test length(interp.reports) === 1
        r = first(interp.reports)
        @test r isa LocalUndefVarErrorReport
        @test r.name === :bar
        @test last(r.vst).line == (@__LINE__)-18
    end

    # try to exclude false negatives as possible (by collecting reports in after-optimization pass)
    let
        interp, frame = analyze_call((Bool,)) do b
            if b
                bar = rand()
            end

            return if b
                return bar # this shouldn't be reported
            else
                return nothing
            end
        end
        @test isempty(interp.reports)
    end

    let
        interp, frame = analyze_call((Bool,)) do b
            if b
                bar = rand()
            end

            return if b
                return nothing
            else
                # ideally we want to have report for this pass, but tons of work will be
                # needed to report this pass
                return bar
            end
        end
        @test_broken length(interp.reports) === 1 &&
            first(interp.reports) isa LocalUndefVarErrorReport &&
            first(interp.reports).name === :bar
    end

    let
        interp, frame = analyze_call((Int,)) do a
            function inner(n)
                if n > 0
                   a = n
                end
            end
            inner(rand(Int))
            return a
        end
        @test isempty(interp.reports)
    end

    # with the current approach, local undefined variables in toplevel frame can't be found
    # since we don't cache toplevel frame and thus it won't be optimized
    let
        res = @analyze_toplevel begin
            foo = let
                if rand(Bool)
                    bar = rand(Int)
                else
                    bar # undefined in this pass
                end
            end
        end
        @test_broken !isempty(res.inference_error_reports)
    end
end

@testset "report undefined (global) variables" begin
    let
        interp, frame = analyze_call(()->foo)
        @test length(interp.reports) === 1
        @test first(interp.reports) isa GlobalUndefVarErrorReport
        @test first(interp.reports).name === :foo
    end

    # deeper level
    let
        m = @fixturedef begin
            foo(bar) = bar + baz
            qux(a) = foo(a)
        end

        interp, frame = Core.eval(m, :($analyze_call(qux, (Int,))))
        @test length(interp.reports) === 1
        @test first(interp.reports) isa GlobalUndefVarErrorReport
        @test first(interp.reports).name === :baz

        # works when cached
        interp, frame = Core.eval(m, :($analyze_call(qux, (Int,))))
        @test length(interp.reports) === 1
        @test first(interp.reports) isa GlobalUndefVarErrorReport
        @test first(interp.reports).name === :baz
    end
end

@testset "report non-boolean condition error" begin
    # simple case
    let
        interp, frame = analyze_call((Int,)) do a
            a ? a : nothing
        end
        @test length(interp.reports) === 1
        er = first(interp.reports)
        @test er isa NonBooleanCondErrorReport
        @test er.t === Int
    end

    # don't report when a type can be `Bool` (Bool ⊑ type)
    let
        interp, frame = analyze_call((Integer,)) do a
            a ? a : nothing
        end
        @test isempty(interp.reports)
    end

    # report union split case
    let
        interp, frame = analyze_call((Union{Nothing,Bool},)) do a
            a ? a : false
        end
        @test length(interp.reports) === 1
        let r = first(interp.reports)
            @test r isa NonBooleanCondErrorReport
            @test r.t == [Nothing]
            @test occursin("for 1 of union split cases", r.msg)
        end
    end

    let
        interp, frame = analyze_call() do
            anyary = Any[1,2,3]
            first(anyary) ? first(anyary) : nothing
        end
        @test isempty(interp.reports) # very untyped, we can't report on this ...
    end

    # `strict_condition_check` configuration
    let
        # `==(::Missing, ::Any)`
        interp, frame = analyze_call((Any,Symbol); strict_condition_check = false) do a, b
            a == b ? 0 : 1
        end
        @test isempty(interp.reports)
        interp, frame = analyze_call((Any,Symbol); strict_condition_check = true) do a, b
            a == b ? 0 : 1
        end
        @test any(interp.reports) do r
            isa(r, NonBooleanCondErrorReport) &&
            r.t == Type[Missing]
        end
    end
end

@testset "inference with abstract global variable" begin
    let
        vmod = gen_virtual_module()
        res = @analyze_toplevel context = vmod virtualize = false begin
            s = "julia"
            sum(s)
        end

        @test is_concrete(vmod, :s)
        test_sum_over_string(res)
    end

    @testset "union assignment" begin
        let
            vmod = gen_virtual_module()
            res = @analyze_toplevel context = vmod virtualize = false begin
                global globalvar
                if rand(Bool)
                    globalvar = "String"
                else
                    globalvar = :Symbol
                end
            end

            @test is_abstract(vmod, :globalvar)
            @test vmod.globalvar.t === Union{String,Symbol}
        end

        let
            vmod = gen_virtual_module()
            res = @analyze_toplevel context = vmod virtualize = false begin
                if rand(Bool)
                    globalvar = "String"
                else
                    globalvar = :Symbol
                end

                foo(s::AbstractString) = length(s)
                foo(globalvar) # union-split no method matching error should be reported
            end

            @test is_abstract(vmod, :globalvar)
            @test vmod.globalvar.t === Union{String,Symbol}
            @test length(res.inference_error_reports) === 1
            er = first(res.inference_error_reports)
            @test er isa NoMethodErrorReport
            @test isa(er.t, Vector) # should be true
        end

        # sequential
        let
            vmod = gen_virtual_module()
            res = @analyze_toplevel context = vmod virtualize = false begin
                if rand(Bool)
                    globalvar = "String"
                else
                    globalvar = :Symbol
                end

                foo(s::AbstractString) = length(s)
                foo(globalvar) # union-split no method matching error should be reported

                globalvar = 10
                foo(globalvar) # no method matching error should be reported
            end

            @test is_concrete(vmod, :globalvar)
            @test is_analyzed(vmod, :globalvar)
            @test isa_analyzed(vmod.globalvar, Int)
            @test length(res.inference_error_reports) === 2
            let er = first(res.inference_error_reports)
                @test er isa NoMethodErrorReport
                @test isa(er.t, Vector)
            end
            let er = last(res.inference_error_reports)
                @test er isa NoMethodErrorReport
                @test !isa(er.t, Vector)
            end
        end
    end
end

@testset "UndefKeywordError" begin
    let
        m = gen_virtual_module()
        interp, frame = Core.eval(m, quote
            foo(a; #= can be undef =# kw) =  a, kw
            $analyze_call(foo, (Any,))
        end)
        @test !isempty(interp.reports)
        @test any(interp.reports) do r
            r isa UndefKeywordErrorReport
            r.err.var === :kw
        end
        # there shouldn't be duplicated report for the `throw` call
        @test !any(Fix2(isa, UncaughtExceptionReport), interp.reports)
    end
end

@testset "DivideError" begin
    let
        apply(f, args...) = f(args...)

        interp, frame = analyze_call() do
            apply(div, 1, 0)
        end
        @test !isempty(interp.reports)
        @test any(Fix2(isa, DivideErrorReport), interp.reports)

        interp, frame = analyze_call() do
            apply(rem, 1, 0)
        end
        @test !isempty(interp.reports)
        @test any(Fix2(isa, DivideErrorReport), interp.reports)

        # JET analysis isn't sound
        interp, frame = analyze_call((Int,Int)) do a, b
            apply(div, a, b)
        end
        @test isempty(interp.reports)
    end
end

@testset "report `throw` calls" begin
    # simplest case
    let
        interp, frame = analyze_call(()->throw("foo"))
        @test !isempty(interp.reports)
        @test first(interp.reports) isa UncaughtExceptionReport
    end

    # throws in deep level
    let
        foo(a) = throw(a)
        interp, frame = analyze_call(()->foo("foo"))
        @test !isempty(interp.reports)
        @test first(interp.reports) isa UncaughtExceptionReport
    end

    # don't report possibly false negative `throw`s
    let
        foo(a) = a ≤ 0 ? throw("a is $(a)") : a
        interp, frame = analyze_call(foo, (Int,))
        @test isempty(interp.reports)
    end

    # constant prop sometimes helps exclude false negatives
    let
        foo(a) = a ≤ 0 ? throw("a is $(a)") : a
        interp, frame = analyze_call(()->foo(0))
        @test !isempty(interp.reports)
        @test first(interp.reports) isa UncaughtExceptionReport
    end

    # report even if there're other "critical" error exist
    let
        m = gen_virtual_module()
        interp, frame = Core.eval(m, quote
            foo(a) = sum(a) # should be reported
            bar(a) = throw(a) # shouldn't be reported first
            $analyze_call((Bool, String)) do b, s
                b && foo(s)
                bar(s)
            end
        end)
        @test length(interp.reports) === 3
        test_sum_over_string(interp.reports)
    end

    # end to end
    let
        # this should report `throw(ArgumentError("Sampler for this object is not defined")`
        interp, frame = analyze_call(rand, (Char,))
        @test !isempty(interp.reports)
        @test first(interp.reports) isa UncaughtExceptionReport

        # this should not report `throw(DomainError(x, "sin(x) is only defined for finite x."))`
        interp, frame = analyze_call(sin, (Int,))
        @test isempty(interp.reports)

        # again, constant prop sometimes can exclude false negatives
        interp, frame = analyze_call(()->sin(Inf))
        @test !isempty(interp.reports)
        @test first(interp.reports) isa UncaughtExceptionReport
    end
end

@testset "constant analysis" begin
    # constant prop should limit false positive union-split no method reports
    let
        m = @fixturedef begin
            mutable struct P
                i::Int
                s::String
            end
            foo(p, i) = p.i = i
        end

        # "for one of the union split cases, no matching method found for signature: Base.convert(Base.fieldtype(Base.typeof(x::P)::Type{P}, f::Symbol)::Union{Type{Int64}, Type{String}}, v::Int64)" should be threw away
        interp, frame = Core.eval(m, :($analyze_call(foo, (P, Int))))
        @test isempty(interp.reports)

        # works for cache
        interp, frame = Core.eval(m, :($analyze_call(foo, (P, Int))))
        @test isempty(interp.reports)
    end

    # more cache test, constant prop should re-run in deeper level
    let
        m = @fixturedef begin
            mutable struct P
                i::Int
                s::String
            end
            foo(p, i) = p.i = i
            bar(args...) = foo(args...)
        end

        # "for one of the union split cases, no matching method found for signature: Base.convert(Base.fieldtype(Base.typeof(x::P)::Type{P}, f::Symbol)::Union{Type{Int64}, Type{String}}, v::Int64)" should be threw away
        interp, frame = Core.eval(m, :($analyze_call(bar, (P, Int))))
        @test isempty(interp.reports)

        # works for cache
        interp, frame = Core.eval(m, :($analyze_call(bar, (P, Int))))
        @test isempty(interp.reports)
    end

    # constant prop should not exclude those are not related
    let
        m = gen_virtual_module()
        interp, frame = Core.eval(m, quote
            mutable struct P
                i::Int
                s::String
            end
            function foo(p, i, s)
                p.i = i
                p.s = s
            end

            $analyze_call(foo, (P, Int, #= invalid =# Int))
        end)

        # "for one of the union split cases, no matching method found for signature: Base.convert(Base.fieldtype(Base.typeof(x::P)::Type{P}, f::Symbol)::Union{Type{Int64}, Type{String}}, v::Int64)" should be threw away, while
        # "no matching method found for call signature: Base.convert(Base.fieldtype(Base.typeof(x::P)::Type{P}, f::Symbol)::Type{String}, v::Int64)" should be kept
        @test length(interp.reports) === 1
        er = first(interp.reports)
        @test er isa NoMethodErrorReport
        @test er.t === Tuple{typeof(convert), Type{String}, Int}
    end

    # constant prop should narrow down union-split no method error to single no method matching error
    let
        m = gen_virtual_module()
        interp, frame = Core.eval(m, quote
            mutable struct P
                i::Int
                s::String
            end
            function foo(p, i, s)
                p.i = i
                p.s = s
            end

            $analyze_call(foo, (P, String, Int))
        end)

        # "for one of the union split cases, no matching method found for signature: Base.convert(Base.fieldtype(Base.typeof(x::P)::Type{P}, f::Symbol)::Union{Type{Int64}, Type{String}}, v::String)" should be narrowed down to "no matching method found for call signature: Base.convert(Base.fieldtype(Base.typeof(x::P)::Type{P}, f::Symbol)::Type{Int}, v::String)"
        @test !isempty(interp.reports)
        @test any(interp.reports) do report
            report isa NoMethodErrorReport &&
            report.t === Tuple{typeof(convert), Type{Int}, String}
        end
        # "no matching method found for call signature: Base.convert(Base.fieldtype(Base.typeof(x::P)::Type{P}, f::Symbol)::Type{String}, v::Int)"
        # won't be reported since `typeinf` early escapes on `Bottom`-annotated statement
    end

    # report-throw away with constant analysis shouldn't throw away reports from the same
    # frame but with the other constants
    let
        m = gen_virtual_module()
        interp, frame = Core.eval(m, quote
            foo(a) = a<0 ? a+string(a) : a
            bar() = foo(-1), foo(1) # constant analysis on `foo(1)` shouldn't throw away reports from `foo(-1)`
            $analyze_call(bar)
        end)
        @test !isempty(interp.reports)
        @test any(r->isa(r,NoMethodErrorReport), interp.reports)
    end

    let
        m = gen_virtual_module()
        interp, frame = Core.eval(m, quote
            foo(a) = a<0 ? a+string(a) : a
            function bar(b)
                a = b ? foo(-1) : foo(1)
                b = foo(-1)
                return a, b
            end
            $analyze_call(bar, (Bool,))
        end)
        @test !isempty(interp.reports)
        # FIXME our report uniquify logic might be wrong and it wrongly singlifies the different reports here
        @test_broken count(isa(report, NoMethodErrorReport) for report in interp.reports) == 2
    end

    @testset "constant analysis throws away false positive reports" begin
        let
            m = @fixturedef begin
                foo(a) = a > 0 ? a : "minus"
                bar(a) = foo(a) + 1
            end

            # constant propagation can reveal the error pass can't happen
            interp, frame = Core.eval(m, :($analyze_call(()->bar(10))))
            @test isempty(interp.reports)

            # for this case, no constant prop' doesn't happen, we can't throw away error pass
            interp, frame = Core.eval(m, :($analyze_call(bar, (Int,))))
            @test length(interp.reports) === 1
            er = first(interp.reports)
            @test er isa NoMethodErrorReport
            @test er.t == [Tuple{typeof(+),String,Int}]

            # if we run constant prop' that leads to the error pass, we should get the reports
            interp, frame = Core.eval(m, :($analyze_call(()->bar(0))))
            @test length(interp.reports) === 1
            er = first(interp.reports)
            @test er isa NoMethodErrorReport
            @test er.t === Tuple{typeof(+),String,Int}
        end

        # we should throw-away reports collected from frames that are revealed as "unreachable"
        # by constant prop'
        let
            m = @fixturedef begin
                foo(a) = bar(a)
                function bar(a)
                    return if a < 1
                        baz1(a, "0")
                    else
                        baz2(a, a)
                    end
                end
                baz1(a, b) = a ? b : b
                baz2(a, b) = a + b
            end

            # no constant prop, just report everything
            interp, frame = Core.eval(m, :($analyze_call(foo, (Int,))))
            @test length(interp.reports) === 1
            er = first(interp.reports)
            @test er isa NonBooleanCondErrorReport &&
                er.t === Int

            # constant prop should throw away the non-boolean condition report from `baz1`
            interp, frame = Core.eval(m, quote
                $analyze_call() do
                    foo(1)
                end
            end)
            @test isempty(interp.reports)

            # constant prop'ed, still we want to have the non-boolean condition report from `baz1`
            interp, frame = Core.eval(m, quote
                $analyze_call() do
                    foo(0)
                end
            end)
            @test length(interp.reports) === 1
            er = first(interp.reports)
            @test er isa NonBooleanCondErrorReport &&
                er.t === Int

            # so `Bool` is good for `foo` after all
            interp, frame = Core.eval(m, :($analyze_call(foo, (Bool,))))
            @test isempty(interp.reports)
        end

        # end to end
        let
            res = @analyze_toplevel begin
                function foo(n)
                    if n < 10
                        return n
                    else
                        return "over 10"
                    end
                end

                function bar(n)
                    if n < 10
                        return foo(n) + 1
                    else
                        return foo(n) * "+1"
                    end
                end

                bar(1)
                bar(10)
            end

            @test isempty(res.inference_error_reports)
        end
    end
end

@testset "keyword argument methods" begin
    interp, frame = Core.eval(gen_virtual_module(), quote
        f(a; b = nothing, c = nothing) = return
        $analyze_call((Any,)) do b
            f(1; b)
        end
    end)
    @test isempty(interp.reports)
end

@testset "don't early escape if type grows up to `Any`" begin
    vmod = gen_virtual_module()
    res = @analyze_toplevel context = vmod virtualize = false begin
        abstract type Foo end
        struct Foo1 <: Foo
            bar
        end
        struct Foo2 <: Foo
            baz # typo
        end
        struct Foo3 <: Foo
            qux # typo
        end
        bar(foo::Foo) = foo.bar

        f = rand(Bool) ? Foo1(1) : rand(Bool) ? Foo2(1) : Foo3(1)
        bar(f)
    end

    # `bar(::Foo1)` is valid but its return type is `Any`, and so we can't collect possible
    # error points for `bar(::Foo2)` and `bar(::Foo3)` if we bail out on `Any`-grew return type
    @test length(res.inference_error_reports) === 2
    @test any(res.inference_error_reports) do er
        return er isa NoFieldErrorReport &&
            er.typ === vmod.Foo2 &&
            er.name === :bar
    end
    @test any(res.inference_error_reports) do er
        return er isa NoFieldErrorReport &&
            er.typ === vmod.Foo3 &&
            er.name === :bar
    end
end

@static isdefined(CC, :abstract_invoke) && @testset "abstract_invoke" begin
    # non-`Type` `argtypes`
    interp, frame = analyze_call() do
        invoke(sin, :this_should_be_type, 1.0)
    end
    @test length(interp.reports) == 1
    r = first(interp.reports)
    @test isa(r, InvalidInvokeErrorReport)

    # invalid `argtype`
    interp, frame = analyze_call() do
        Base.@invoke sin(1.0::Int)
    end
    @test length(interp.reports) == 1
    r = first(interp.reports)
    @test isa(r, InvalidInvokeErrorReport)

    # don't report errors collected in `invoke`d functions
    foo(i::Integer) = throw(string(i))
    interp, frame = analyze_call((Any,)) do a
        Base.@invoke foo(a::Integer)
    end
    @test !isempty(interp.reports)
    @test !any(r->isa(r, InvalidInvokeErrorReport), interp.reports)
end

@testset "additional analysis pass for task parallelism code" begin
    # general case with `schedule(::Task)` pattern
    interp, frame = analyze_call() do
        t = Task() do
            sum("julia")
        end
        schedule(t)
        fetch(t)
    end
    test_sum_over_string(interp)

    # handle `Threads.@spawn` (https://github.com/aviatesk/JET.jl/issues/114)
    interp, frame = analyze_call() do
        fetch(Threads.@spawn 1 + "foo")
    end
    @test length(interp.reports) == 1
    let r = first(interp.reports)
        @test isa(r, NoMethodErrorReport)
        @test r.t === Tuple{typeof(+), Int, String}
    end

    # handle `Threads.@threads`
    interp, frame = analyze_call((Int,)) do n
        a = String[]
        Threads.@threads for i in 1:n
            push!(a, i)
        end
        return a
    end
    @test !isempty(interp.reports)
    @test any(interp.reports) do r
        isa(r, NoMethodErrorReport) &&
        r.t === Tuple{typeof(convert), Type{String}, Int}
    end

    # multiple tasks in the same frame
    interp, frame = analyze_call() do
        t1 = Threads.@spawn 1 + "foo"
        t2 = Threads.@spawn "foo" + 1
        fetch(t1), fetch(t2)
    end
    @test length(interp.reports) == 2
    let r = interp.reports[1]
        @test isa(r, NoMethodErrorReport)
        @test r.t === Tuple{typeof(+), Int, String}
    end
    let r = interp.reports[2]
        @test isa(r, NoMethodErrorReport)
        @test r.t === Tuple{typeof(+), String, Int}
    end

    # nested tasks
    interp, frame = analyze_call() do
        t0 = Task() do
            t = Threads.@spawn sum("julia")
            fetch(t)
        end
        schedule(t0)
        fetch(t0)
    end
    test_sum_over_string(interp)

    # when `schedule` call is separated from `Task` definition
    make_task(s) = Task() do
        sum(s)
    end
    function run_task(t)
        schedule(t)
        fetch(t)
    end
    interp, frame = analyze_call() do
        t = make_task("julia")

        run_task(t)
    end
    test_sum_over_string(interp)
    let r = first(interp.reports)
        # we want report to come from `run_task`, but currently we invoke JET analysis on `Task` construction
        @test_broken any(r.vst) do vf
            vf.linfo.def.name === :run_task
        end
    end

    # report uncaught exception happened in a task
    interp, frame = analyze_call() do
        fetch(Threads.@spawn throw("foo"))
    end
    @test length(interp.reports) == 1
    @test isa(first(interp.reports), UncaughtExceptionReport)

    # don't fail into infinite loop (rather, don't spoil inference termination)
    m = @fixturedef begin
        # adapated from https://julialang.org/blog/2019/07/multithreading/
        import Base.Threads.@spawn

        # sort the elements of `v` in place, from indices `lo` to `hi` inclusive
        function psort!(v, lo::Int=1, hi::Int=length(v))
            if lo >= hi                       # 1 or 0 elements; nothing to do
                return v
            end
            if hi - lo < 100000               # below some cutoff, run in serial
                sort!(view(v, lo:hi), alg = MergeSort)
                return v
            end

            mid = (lo+hi)>>>1                 # find the midpoint

            half = @spawn psort!(v, lo, mid)  # task to sort the lower half; will run
            psort!(v, mid+1, hi)              # in parallel with the current call sorting
                                              # the upper half
            wait(half)                        # wait for the lower half to finish

            temp = v[lo:mid]                  # workspace for merging

            i, k, j = 1, lo, mid+1            # merge the two sorted sub-arrays
            @inbounds while k < j <= hi
                if v[j] < temp[i]
                    v[k] = v[j]
                    j += 1
                else
                    v[k] = temp[i]
                    i += 1
                end
                k += 1
            end
            @inbounds while k < j
                v[k] = temp[i]
                k += 1
                i += 1
            end

            return v
        end
    end
    interp, frame = analyze_call(m.psort!, (Vector{Int},))
    @test true
end

@static if VERSION ≥ v"1.7.0-DEV.705"

@testset "opaque closure" begin
    # can cache const prop' result with varargs
    function oc_varargs_constprop()
        oc = Base.Experimental.@opaque (args...)->args[1]+args[2]+arg[3] # typo on `arg[3]`
        return Val{oc(1,2,3)}()
    end
    interp, = @analyze_call oc_varargs_constprop()
    @test !isempty(interp.cache)
end

end # @static if VERSION ≥ v"1.7.0-DEV.705"

@testset "https://github.com/aviatesk/JET.jl/issues/133" begin
    res = @analyze_toplevel begin
        @ccall strlen("foo"::Cstring)::Csize_t
    end
    @test isempty(res.inference_error_reports)
end

@testset "staged programming" begin
    m = @fixturedef begin
        @generated function foo(a)
            if a <: Integer
                return :(a)
            elseif a <: Number
                return :(undefvar) # report me this case
            end
            throw("invalid argument")
        end
    end

    # successful code generation, valid code
    let
        interp, frame = analyze_call(m.foo, (Int,))
        @test !isnothing(frame) # code generation should be successful
        @test isempty(interp.reports)
    end

    # successful code generation, invalid code
    let
        interp, frame = analyze_call(m.foo, (Float64,))
        @test !isnothing(frame) # code generation should be successful
        @test length(interp.reports) == 1
        r = first(interp.reports)
        @test isa(r, GlobalUndefVarErrorReport)
        @test r.name === :undefvar
    end

    # unsuccessful code generation
    let
        interp, frame = analyze_call(m.foo, (String,))
        @test isnothing(frame) # code generation should be unsuccessful
        @test length(interp.reports) == 1
        r = first(interp.reports)
        @test isa(r, GeneratorErrorReport) && r.err == "invalid argument"
    end
end

@testset "infinite iteration" begin
    m = @fixturedef begin
        struct NeverTerminate
            val::Int
        end
        Base.iterate(nv::NeverTerminate, state = 0) =
            state>nv.val ? (state, state+1) : (state, state+1)
    end

    let # iteration protocol
        interp, frame = @eval m $analyze_call((Int,)) do n
            for a in NeverTerminate(n)
                println(a)
            end
        end
        @test any(interp.reports) do r
            isa(r, InfiniteIterationErrorReport) &&
            r.typ === m.NeverTerminate &&
            any(r.vst) do vf
                vf.line == (@__LINE__)-8
            end
        end
    end

    let # iteration protocol, nested
        interp, frame = @eval m $analyze_call((Int,)) do n
            for a in 1:n
                for b in NeverTerminate(a)
                    println(b)
                end
            end
        end
        @test any(interp.reports) do r
            isa(r, InfiniteIterationErrorReport) &&
            r.typ === m.NeverTerminate &&
            any(r.vst) do vf
                vf.line == (@__LINE__)-9
            end
        end
    end

    let # iteration protocol, on container type
        interp, frame = @eval m $analyze_call((Int,)) do n
            sum((a for a in NeverTerminate(n))...)
        end
        @test any(interp.reports) do r
            isa(r, InfiniteIterationErrorReport)
        end
    end

    let # complicated control flow, no false positive
        interp, frame = analyze_call((Char,Tuple{Char,Char})) do x, itr
            # adapated from https://github.com/JuliaLang/julia/blob/24d9eab45632bdb3120c9e664503745eb58aa2d6/base/operators.jl#L1278-L1297
            anymissing = false
            for y in itr
                v = (y == x)
                if ismissing(v)
                    anymissing = true
                elseif v
                    return true
                end
            end
            return anymissing ? missing : false
        end
        @test isempty(interp.reports)
    end

    let # general case of "this function never return"
        # NOTE comes down to `Base._foldl_impl`
        interp, frame = @eval m $analyze_call((Int,)) do n
            sum(a for a in NeverTerminate(n))
        end
        @test_broken any(interp.reports) do r
            isa(r, InfiniteIterationErrorReport) &&
            r.typ === m.NeverTerminate
        end
    end
end
