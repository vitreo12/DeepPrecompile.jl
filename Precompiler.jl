module Precompiler

using Crayons

export find_invoke_functions, precompile_functions, find_and_precompile

#=
This package does 2 things:

1) Generate THOROUGH precompile statements for PackageCompiler.jl

2) Generate complete precompile statements to be used in interactive sessions

=#

#=
Modus operandi:

For PackageCompiler.jl:

1) Make sure (with a @fully_precompile macro) all the inner functions used in the generation of precompile statements
   will get added to the precompile.jl generated by PackageCompiler.jl.

2) Introspect EVERY call to any function, recursively, and expose each call (with set types) to PackageCompiler.jl's snooping.

Things to watch for:
    1) code_lowered(Function, (Tuple for args))
    2) Base.method_instances(Function, (Tuple for args))
=#

function find_and_precompile(f, types_tuple)
    println(Crayon(foreground = :white), "Running snooping and precompilation on: ", Crayon(foreground = :yellow), "$f", Crayon(foreground = :blue), "$types_tuple")
    println()
    println(Crayon(foreground = :white), "Snooping...")

    method_dict = find_invoke_functions(f, types_tuple)

    println()
    println(Crayon(foreground = :white), "Precompiling...")
    
    precompile_functions(method_dict)
    
    #Reset Crayon to white
    println(Crayon(foreground = :white))
end

function precompile_functions(method_dict)
    for entry in method_dict

        function_name = entry[1][1]
        tuple_types = entry[1][2]

        #entry[1] is a GlobalRef. eval everything and treat as Symbols to escape the problem.
        has_precompiled = eval(:(precompile($function_name, $tuple_types)))

        if(has_precompiled)
            println(Crayon(foreground = :white), "Precompiling ", Crayon(foreground = :yellow), "$function_name", Crayon(foreground = :blue), "$tuple_types ", Crayon(foreground = :white), "-> ", Crayon(foreground = :green), "Succesfully precompiled")
        else
            println(Crayon(foreground = :white), "Precompiling ", Crayon(foreground = :yellow), "$function_name", Crayon(foreground = :blue), "$tuple_types ", Crayon(foreground = :white), "-> ", Crayon(foreground = :red), "Failed to precompile")
        end
    end
end

#Returns true if method was added, false if the method was already in the table.
function add_to_method_dict(method_dict, f, types_tuple)::Bool
    
    tuple_fun_and_types = (f, types_tuple)
    
    try
        getindex(method_dict, tuple_fun_and_types)
        #println(Crayon(foreground = :red), "WARNING: ", Crayon(foreground = :white), "Function $f$(types_tuple) is already in the method dictionary")
    catch
        setindex!(method_dict, tuple_fun_and_types, tuple_fun_and_types)
        return true
    end

    return false
end

function find_invoke_functions(f, types_tuple)    
    method_dict = Dict{Any, Any}()

    find_invoke_functions_recursive(f, types_tuple, method_dict)

    #Dict that will contain PathToFunction => TupleArguments
    return method_dict
end

#Inner types of the Tuple. Recursive search
function find_unstable_type_recursive(type_to_analyze, father_type_vec = nothing, func_name = nothing)

    if(isa(type_to_analyze, DataType))

        #struct / mutable struct search
        for type_svec in type_to_analyze.types
            
            #If it's not a svec, it means we reached the bottom of the graph for this struct
            if(typeof(type_svec) != Core.SimpleVector)
                
                if(!isconcretetype(type_svec))
                    println(Crayon(foreground = :red), "WARNING: ", Crayon(foreground = :white), "Type $type_svec in $type_to_analyze is not concrete")
                    return
                end
                
                #Go to next element if no errors
                continue
            end

            #The struct hasn't been fully checked yet.
            for type in type_svec
                
                if(!isconcretetype(type))
                    println(Crayon(foreground = :red), "WARNING: ", Crayon(foreground = :white), "Type $type in $type_to_analyze is not concrete")
                    return
                end

                find_unstable_type_recursive(type, type_svec)
            end
        end

        #If code gets here, it's a normal DataType (not a composed struct). Just check if it is concrete
        if(!isconcretetype(type_to_analyze))
            if(father_type_vec != nothing && func_name != nothing)
                println(Crayon(foreground = :red), "WARNING: ", Crayon(foreground = :white), "Type $type_to_analyze in $func_name$father_type_vec is not concrete")
            elseif(father_type_vec != nothing)
                println(Crayon(foreground = :red), "WARNING: ", Crayon(foreground = :white), "Type $type_to_analyze in $father_type_vec is not concrete")
            else
                println(Crayon(foreground = :red), "WARNING: ", Crayon(foreground = :white), "Type $type_to_analyze is not concrete")
            end

            return
        end
    end

    if(isa(type_to_analyze, UnionAll))
        println(Crayon(foreground = :red), "WARNING: ", Crayon(foreground = :white), "Type $type_to_analyze is not concrete. Perhaps it hasn't been parametrized correctly.")
        return
    end

    if(isa(type_to_analyze, Union))
        println(Crayon(foreground = :red), "WARNING: ", Crayon(foreground = :white), "$type_to_analyze will generate non-specialized code.")

        #Find inner types in the Union anyway
        find_unstable_type_recursive(type_to_analyze.a, type_to_analyze)
        find_unstable_type_recursive(type_to_analyze.b, type_to_analyze)
    end

end

function find_invoke_functions_recursive(f, types_tuple, method_dict)

    #Print out
    println(Crayon(foreground = :white), "Snooping ", Crayon(foreground = :yellow), "$f", Crayon(foreground = :blue), "$types_tuple")

    #################################
    #Checks for constructor functions

    if(isa(f, DataType))
        
        #Ignore if analyzed DataType is a subtype of Exception
        if(f.super != Exception)
            if(!f.isconcretetype)
                println(Crayon(foreground = :red), "WARNING: ", Crayon(foreground = :white), "Type $f is not concrete")
            end

            for type_of_field in f.types
                if(isa(type_of_field, Union))
                    println(Crayon(foreground = :red), "WARNING: ", Crayon(foreground = :white), "$type_of_field in $f is not concrete.")
                end

                if(isa(type_of_field, UnionAll))
                    println(Crayon(foreground = :red), "WARNING: ", Crayon(foreground = :white), "$type_of_field in $f is not concrete. Perhaps it hasn't been parametrized correctly.")
                end

                if(!type_of_field.isconcretetype)
                    println(Crayon(foreground = :red), "WARNING: ", Crayon(foreground = :white), "Type $type_of_field in $f is not concrete")
                end
            end
        end

    end

    if(isa(f, Union))
        println(Crayon(foreground = :red), "WARNING: ", Crayon(foreground = :white), "$f is not concrete.")
    end

    if(isa(f, UnionAll))
        println(Crayon(foreground = :red), "WARNING: ", Crayon(foreground = :white), "Type $f is not concrete. Perhaps it hasn't been parametrized correctly.")
    end
    #################################

    #Types in the arguments tuple to function
    for type in types_tuple
        find_unstable_type_recursive(type, types_tuple, f)
    end

    #Get the full typed graph for the function
    code_info_typed = code_typed(f, types_tuple)[1].first

    #Cache the top function.
    method_added = add_to_method_dict(method_dict, f, types_tuple)
    if(!method_added)
        return
    end

    #Get the code line by line
    code_line_by_line = code_info_typed.code

    #Get the ssavaluetypes of the code line by line
    code_ssavaluetypes = code_info_typed.ssavaluetypes
    
    #println("$f, $types_tuple")

    #Count the 1 at the beginning of loop to ignore the if/continue stuff that would screw up the counting.
    line_counter = 0

    #Parse the typed graph of the function line by line. Eventually go into each invoke call recursively.
    for code_line in code_line_by_line
        
        line_counter = line_counter + 1

        #If it is a Core.PiNode, it needs to be evaluated first. 
        #Then, its type will be stored at the same position in the code_ssavaluetypes array, substituing the previous one.
        #This way, the actual evaluated typed value will be retrieved later when dealing with the correct ssavalue
        if(isa(code_line, Core.PiNode))

            #The eventual error here, if the Core.PiNode.val is a Core.SSAValue (e.g. "π (%12, Float64)") will be catched by the try/cath block...
            type_of_line = typeof(eval(code_line))
            code_ssavaluetypes[line_counter] = type_of_line
            
            #If the .val of Core.PiNode is a Core.SSAValue, skip it. (e.g. "π (%12, Float64)")
            #I don't know why this hangs forever:
            #if(!isa(code_line.val, Core.SSAValue))
            #    type_of_line = typeof(eval(code_line))
            #    code_ssavaluetypes[line_counter] = type_of_line
            #end

        elseif(isa(code_line, Expr))
            
            #Invoke calls (:invoke)
            if(code_line.head == :invoke)
                invoke_call = code_line
                
                method_instance = invoke_call.args[1]
                #println(method_instance)

                method_instance_name = method_instance.def.name
                #println(method_instance_name)

                method_instance_definition = invoke_call.args[2]
                #println(method_instance_definition)

                method_instance_args = method_instance.specTypes.parameters[2:end] #Ignore first one, which is the function name
                #println(method_instance_args)

                method_instance_args_tuple = tuple(method_instance_args...) #"method_instance_args..." to unpack the svec in all its components
                #println(method_instance_args_tuple)

                invoke_method_added = add_to_method_dict(method_dict, method_instance_definition, method_instance_args_tuple)
                if(!invoke_method_added)
                    continue
                end
                #println(method_dict)
                
                #eval(:(Main.code_warntype($method_instance_name, $method_instance_args_tuple)))
                
                #This will check if the sub invoke calls give type errors. It it does, skip the method entirely.
                try
                    eval(:(find_invoke_functions_recursive($method_instance_definition, $method_instance_args_tuple, $method_dict))) #need to wrap in expr because the "method_instance_name" is a Symbol
                catch exception

                    #Ignore the case of the ErrorException("access to invalid SSAValue"). See above on the if(isa(code_line, Core.PiNode)) block why.
                    if (exception != ErrorException("access to invalid SSAValue"))
                        println(Crayon(foreground = :red), "EXCEPTION DETECTED for $method_instance_definition: ", Crayon(foreground = :white), exception)
                    end
                    
                    continue
                end

            #Function calls (:call)
            elseif(code_line.head == :call)
                call_function_name = code_line.args[1]

                eval_call_function_name = eval(:($call_function_name))

                #println(call_function_name)

                #If it is a Core.IntrinsicFunction or a Core.Builtin function, it's already compiled and no need to do anything with it.
                if(isa(eval_call_function_name, Core.IntrinsicFunction) || isa(eval_call_function_name, Core.Builtin))
                    continue
                end

                #println(call_function_name)

                function_args = code_line.args[2:end]

                call_vec_int_ssavals = Vector{Int64}()
                
                #There might be cases where it's not just a ssavalue in the args for the :call, 
                #but some other things for built-in functions. Like "Base.getfield(%1, :hi)". Ignore such cases.
                mixed_ssavalue = false

                #Find the SSAValue inside the code for this specific :call
                for function_arg in function_args
                    if(isa(function_arg, Core.SSAValue))
                        append!(call_vec_int_ssavals, function_arg.id)
                    else
                        mixed_ssavalue = true
                    end
                end

                if(!isempty(call_vec_int_ssavals) && !mixed_ssavalue)
                    call_vec_types = Vector{Any}(undef, length(call_vec_int_ssavals))
                    call_counter = 1
                    
                    #Retrieve the types of the values in the ssavaluetypes Array through the SSAValue index
                    for num in call_vec_int_ssavals
                        call_vec_types[call_counter] = code_ssavaluetypes[num]
                        call_counter = call_counter + 1
                    end    
                    
                    #Final tuple of arguments
                    call_tuple_types = tuple(call_vec_types...)

                    #Add to precompile Vector
                    call_method_added = add_to_method_dict(method_dict, call_function_name, call_tuple_types)
                    if(!call_method_added)
                        continue
                    end

                    #println("$call_function_name, $call_tuple_types")
                    
                    #Keep recursively find new stuff
                    try
                        eval(:(find_invoke_functions_recursive($call_function_name, $call_tuple_types, $method_dict))) #need to wrap in expr because the "method_instance_name" is a Symbol
                    catch exception
                        #Ignore the case of the ErrorException("access to invalid SSAValue"). See above on the if(isa(code_line, Core.PiNode)) block why.
                        if (exception != ErrorException("access to invalid SSAValue"))
                            println(Crayon(foreground = :red), "EXCEPTION DETECTED for $method_instance_definition: ", Crayon(foreground = :white), exception)
                        end
                        
                        continue
                    end
                end

            #Constructor calls (:new)
            elseif(code_line.head == :new)
                constructor_call = code_line
                constructor_type = eval(:($(constructor_call.args[1]))) #This is a DataType

                typeassert(constructor_type, DataType)

                #They most often will be Core.SSAValues, but they can be String if they are prebaked in.
                constructor_args_code = constructor_call.args[2:end]

                #Actual types of the constructor_type function.
                constructor_args = constructor_type.types

                #Empty vector to fill if some of the types in constructor_args_code are concrete subtypes of constructor_args
                constructor_args_new_vec = Vector{Any}(undef, length(constructor_args))

                println(Crayon(foreground = :white), "Snooping ", Crayon(foreground = :yellow), "$constructor_type", Crayon(foreground = :blue), "$(tuple(constructor_args...))")

                constructor_counter = 1

                for type_of_field in constructor_args

                    if(isa(type_of_field, Union))
                        println(Crayon(foreground = :red), "WARNING: ", Crayon(foreground = :white), "$type_of_field in $constructor_type is not concrete.")

                    elseif(isa(type_of_field, UnionAll))
                        println(Crayon(foreground = :red), "WARNING: ", Crayon(foreground = :white), "$type_of_field in $constructor_type is not concrete. Perhaps it hasn't been parametrized correctly.")
                    
                    elseif(!isconcretetype(type_of_field))
                        println(Crayon(foreground = :red), "WARNING: ", Crayon(foreground = :white), "Type $type_of_field in $constructor_type is not concrete")
                    end

                    #First of all, just fill the empty vector with the standard tuple() values for this constructor
                    constructor_args_new_vec[constructor_counter] = type_of_field

                    #Check if any type in the args to the :new Expr are baked in (mostly, String values)
                    type_in_constructor_args_code = typeof(constructor_args_code[constructor_counter])

                    #First check if the argument is directly inserted as subtype in the graph (as the case for String(s) in AbstractString(s) functions, check code_typed(rand, (Int64, Int64) and its AssertionError fuction))
                    if(isconcretetype(type_in_constructor_args_code) && isa(type_of_field, Type) && type_of_field != Any)
                        if(type_in_constructor_args_code <: type_of_field)
                            constructor_args_new_vec[constructor_counter] = type_in_constructor_args_code
                            println(Crayon(foreground = :green), "FOUND ", Crayon(foreground = :white), "$type_in_constructor_args_code as concrete subtype of $type_of_field. Using $type_in_constructor_args_code" )
                        end
                    end

                    constructor_counter = constructor_counter + 1
                end

                constructor_args_tuple = tuple(constructor_args_new_vec...)

                constructor_method_added = add_to_method_dict(method_dict, constructor_type, constructor_args_tuple)
                if(!constructor_method_added)
                    continue
                end
            end
        end
    end
end

end


#TESTING:
module TypeStabilityTest

export myStruct, test_calc

using ..Precompiler

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

function test_precompiler()

    find_and_precompile(myStruct{Float64, Int64}, (Float64, Int64))

    find_and_precompile(test_calc, (myStruct{Float64, Int64}, ))

    #find_and_precompile(myUnstableStruct, (Float64, Int64))

    #find_invoke_functions(myStruct{Float64, Int64}, (Float64, Int64))

    #The resulting fields in myStruct{Float64, Int64} are seen as concrete.
    #find_invoke_functions(test_calc, (myStruct{Float64, Int64}, ))

    #find_invoke_functions(myUnstableStruct, (Float64, Int64))
end

#test_warntypes()

#test_precompiler()

end

#MAIN

#using Plots

function test_precompiler()

    Precompiler.find_and_precompile(TypeStabilityTest.myStruct{Float64, Int64}, (Float64, Int64))

    Precompiler.find_and_precompile(TypeStabilityTest.test_calc, (TypeStabilityTest.myStruct{Float64, Int64}, ))

    Precompiler.find_and_precompile(TypeStabilityTest.myUnstableStruct, (Float64, Int64))

    Precompiler.find_and_precompile(rand, (Int64, Int64))

    Precompiler.find_and_precompile(zeros, (Int64,))

    #Precompiler.find_and_precompile(plotly, ())

    #Precompiler.find_and_precompile(plot, (Array{Float64, 2},))
end

function manual_precompiler()
    precompile(sin, (Float64,))
    precompile(cos, (Float64,))
    precompile(tanh, (Float64,))

    #How do i retrieve all these println calls coming form a :call?
    precompile(println, (Float64,))
    precompile(println, (Base.TTY, Float64))
    precompile(Base.print, (Base.TTY, Float64, Char))
end

test_precompiler()
#manual_precompiler()

#PROBLEM WITH PRECOMPILER NOW IS THE :call STUFF, which, for exampled is used
#for println function, which is not getting throughly precompiled.

#I could just print a Warning for untyped methods from Base, Core, etc... To just check on user defined STUFF
#giving for granted that Julia inner code is type stable.

@time a = 100
@time b = TypeStabilityTest.myStruct{Float64, Int64}(16.214124, 10)
@time TypeStabilityTest.test_calc(b)

@time TypeStabilityTest.myUnstableStruct(16.214124, 10)
@time rand_vec = rand(5, 10)
@time rand_vec = zeros(1000)

#plotly()

#plot(rand_vec, linewidth=2, title="My Plot")