module TypeStabilityTest

abstract type AbstractStruct end

#=
If using a::AbstractFloat, a will always be an AbstractFloat throughout the code, even if it assigned a concrete type.
Using parametric types, I can make sure to instantiate the EXACT type!!!!!!!!
=#

struct myStruct{F <: Union{AbstractFloat, Signed}, S <: Union{AbstractFloat, Signed}} <: AbstractStruct
    a::F
    b::S
end

struct myUnstableStruct <: AbstractStruct
    a::Union{AbstractFloat, Signed}
    b::Union{AbstractFloat, Signed}
end

function hello(a::AbstractFloat)
    b = floor(a)
    c = b * a
    d = c - b
    f = tanh(d)
    return f
end

function test_calc(input::AbstractStruct)
    sine_val = sin(input.a * 2pi)
    sine_val2 = cos(input.b * 2pi)
    final_val = mod(sine_val, hello(sine_val2))
    println(final_val)
    return final_val
end

function cubic_interp(a::AbstractFloat, x0::AbstractFloat, x1::AbstractFloat, x2::AbstractFloat, x3::AbstractFloat)
    c0::Float32 = x1
    c1::Float32 = 0.5f0 * (x2 - x0)
    c2::Float32 = x0 - (2.5f0 * x1) + (2.0f0 * x2) - (0.5f0 * x3)
    c3::Float32 = 0.5f0 * (x3 - x0) + (1.5f0 * (x1 - x2))
    out_value::Float32 = (((((c3 * a) + c2) * a) + c1) * a) + c0
    return out_value
end

function test_warntypes()

    println("\n************** PARAMETRIC TYPE *****************\n")
    #Stable (using parametric types)
    Main.code_warntype(test_calc, (myStruct{Float64, Int64}, ))

    #Unstable 
    println("\n************** UNSTABLE TYPE *****************\n")
    t::myUnstableStruct = myUnstableStruct(Float64(123.3), Int64(2)) #Even if declaring this..
    Main.@code_warntype test_calc(t)

    #Stable
    println("\n************** PARAMETRIC FUNCTION *****************\n")
    Main.code_warntype(cubic_interp, (Float32, Float64, Float16, Float32, Float64))
end

test_warntypes()

end