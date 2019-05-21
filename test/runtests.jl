#TESTING:
module TypeStabilityTest

export myStruct, test_calc

using DeepPrecompile

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
    a::AbstractFloat
    b::Signed
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

    #Stable (using parametric types)
    println("\n************** PARAMETRIC TYPE *****************\n")
    Main.code_warntype(test_calc, (myStruct{Float64, Int64}, ))

    #Unstable 
    println("\n************** UNSTABLE TYPE *****************\n")
    t::myUnstableStruct = myUnstableStruct(Float64(123.3), Int64(2)) #Even if declaring this..
    Main.@code_warntype test_calc(t)

    #Stable
    println("\n************** PARAMETRIC FUNCTION *****************\n")
    Main.code_warntype(cubic_interp, (Float32, Float64, Float16, Float32, Float64))

end

function test_DeepPrecompile()

    deep_precompile(myStruct{Float64, Int64}, (Float64, Int64))

    deep_precompile(test_calc, (myStruct{Float64, Int64}, ))

    #deep_precompile(myUnstableStruct, (Float64, Int64))

    #find_compilable_methods(myStruct{Float64, Int64}, (Float64, Int64))

    #The resulting fields in myStruct{Float64, Int64} are seen as concrete.
    #find_compilable_methods(test_calc, (myStruct{Float64, Int64}, ))

    #find_compilable_methods(myUnstableStruct, (Float64, Int64))
end

#test_warntypes()

#test_DeepPrecompile()

end


using LinearAlgebra

using Crayons

function func_with_everything()
    
    b = TypeStabilityTest.myStruct{Float64, Int64}(16.214124, 10)
    c = TypeStabilityTest.test_calc(b)

    t = TypeStabilityTest.myUnstableStruct(16.214124, 10)
    g = rand_vec = rand(10, 10)
    h = det(rand_vec)
    k = zeros_vec = zeros(1000)

    println(Crayon(foreground = :green), "CRAYON ", Crayon(foreground = :white))

    return c
end


function test_DeepPrecompile()
    DeepPrecompile.deep_precompile(func_with_everything, ())
end

test_DeepPrecompile()

@time func_with_everything()

@time func_with_everything()