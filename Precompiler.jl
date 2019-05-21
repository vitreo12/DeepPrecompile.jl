module Precompiler

using Crayons

using InteractiveUtils

export @deep_precompile, @deep_precompile_list, deep_precompile, deep_precompile_list

#Using InteractiveUtils.gen_call_with_extracted_types_and_kwargs to turn the args into arg types, as used in @code_typed, etc...
macro deep_precompile(ex0...)
    InteractiveUtils.gen_call_with_extracted_types_and_kwargs(__module__, :deep_precompile, ex0)
end

macro deep_precompile_list(ex0...)
    InteractiveUtils.gen_call_with_extracted_types_and_kwargs(__module__, :deep_precompile_list, ex0)
end

function deep_precompile(f, types_tuple) 
    #Check if f is a valid callable function/constructor.
    #methods will already throw an error if the function is not defined.
    method_list = methods(f).ms 
    if(length(method_list) < 1)
        error("Function $f has no callable methods.")
    end

     #Unpack args if using @deep_precompile, which returns a Tuple{ArgType,...}, which is not an instantiated Tuple, but a dispatched tuple.
     if(!isa(types_tuple, Tuple))
        if(typeof(types_tuple) == DataType && types_tuple.isdispatchtuple) #args from the macro version
            types_tuple = tuple(types_tuple.parameters...) #Unpack the parametric Tuple into a instantiated Tuple(). Tuple{Int64, Float64} -> (Int64, Float64)
        else
            error("Invalid argument: $types_tuple")
        end
    end

    println(Crayon(foreground = :white), "-------------------------------------------------------------------------------")
    println(Crayon(foreground = :white), "| Running snooping and precompilation on: ", Crayon(foreground = :yellow), "$f", Crayon(foreground = :blue), "$types_tuple", Crayon(foreground = :white), "...")
    println(Crayon(foreground = :white), "|")
    println(Crayon(foreground = :white), "| Snooping...")

    #Dict with all methods/tuple of types pairs
    method_dict = find_compilable_methods(f, types_tuple)
 
    #Vector of precompile Exprs. 
    precompile_list = generate_precompile_list(method_dict)

    println(Crayon(foreground = :white), "|")
    println(Crayon(foreground = :white), "| Precompiling...")

    #Actual precompilation of all the methods
    precompile_methods(method_dict, precompile_list)
    
    #Reset Crayon to white
    println(Crayon(foreground = :white), "-------------------------------------------------------------------------------")
end

#Just return the precompile_list as a Vector{Expr}
function deep_precompile_list(f, types_tuple)
    #Check if f is a valid callable function/constructor.
    #methods will already throw an error if the function is not defined.
    method_list = methods(f).ms 
    if(length(method_list) < 1)
        error("Function $f has no callable methods.")
    end

    #Unpack args if using @deep_precompile, which returns a Tuple{ArgType,...}, which is not an instantiated Tuple, but a dispatched tuple.
    if(!isa(types_tuple, Tuple))
        if(typeof(types_tuple) == DataType && types_tuple.isdispatchtuple) #args from the macro version
            types_tuple = tuple(types_tuple.parameters...) #Unpack the parametric Tuple into a instantiated Tuple(). Tuple{Int64, Float64} -> (Int64, Float64)
        else
            error("Invalid argument: $types_tuple")
        end
    end
    
    println(Crayon(foreground = :white), "-------------------------------------------------------------------------------")
    println(Crayon(foreground = :white), "| Running snooping and precompilation on: ", Crayon(foreground = :yellow), "$f", Crayon(foreground = :blue), "$types_tuple", Crayon(foreground = :white), "...")
    println(Crayon(foreground = :white), "|")
    println(Crayon(foreground = :white), "| Snooping...")

    #Dict with all methods/tuple of types pairs
    method_dict = find_compilable_methods(f, types_tuple)
    
    #Vector of precompile Exprs. Separated from the actual precompilation in order to be also used in PackageCompiler.jl
    precompile_list = generate_precompile_list(method_dict)

    println(Crayon(foreground = :white))
    
    #Only return the precompile_list of Exprs
    return precompile_list
end

function generate_precompile_list(method_dict)
    precompile_list = Vector{Expr}(undef, length(method_dict))

    counter = 1
    for entry in method_dict
        function_name = entry[1][1]
        tuple_types = entry[1][2]

        precompile_list[counter] = :(precompile($function_name, $tuple_types))

        counter = counter + 1
    end

    return precompile_list
end

function precompile_methods(method_dict, precompile_list)
    counter = 1
    for entry in method_dict
        precompile_expr = precompile_list[counter]
        typeassert(precompile_expr, Expr)

        has_precompiled = eval(precompile_expr)

        function_name = entry[1][1]
        tuple_types = entry[1][2]

        if(has_precompiled)
            println(Crayon(foreground = :white), "| Precompiling ", Crayon(foreground = :yellow), "$function_name", Crayon(foreground = :blue), "$tuple_types ", Crayon(foreground = :white), "-> ", Crayon(foreground = :green), "Succesfully precompiled.")
        else
            println(Crayon(foreground = :white), "| Precompiling ", Crayon(foreground = :yellow), "$function_name", Crayon(foreground = :blue), "$tuple_types ", Crayon(foreground = :white), "-> ", Crayon(foreground = :red), "Failed to precompile.")
        end

        counter = counter + 1
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

function find_compilable_methods(f, types_tuple)    
    method_dict = Dict{Any, Any}()

    find_compilable_methods_recursive(f, types_tuple, method_dict)

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
                    println(Crayon(foreground = :magenta), "| WARNING: ", Crayon(foreground = :white), "Type ", Crayon(foreground = :blue), "$type_svec ", Crayon(foreground = :white), "in ", Crayon(foreground = :yellow), "$type_to_analyze ", Crayon(foreground = :white), "is not concrete.")
                    return
                end
                
                #Go to next element if no errors
                continue
            end

            #The struct hasn't been fully checked yet.
            for type in type_svec
                
                if(!isconcretetype(type))
                    println(Crayon(foreground = :magenta), "| WARNING: ", Crayon(foreground = :white), "Type ", Crayon(foreground = :blue), "$type ", Crayon(foreground = :white), "in ", Crayon(foreground = :yellow), "$type_to_analyze ", Crayon(foreground = :white), "is not concrete.")
                    return
                end

                find_unstable_type_recursive(type, type_svec)
            end
        end

        #If code gets here, it's a normal DataType (not a composed struct). Just check if it is concrete
        if(!isconcretetype(type_to_analyze))
            if(father_type_vec != nothing && func_name != nothing)
                println(Crayon(foreground = :magenta), "| WARNING: ", Crayon(foreground = :white), "Type ", Crayon(foreground = :blue), "$type_to_analyze ", Crayon(foreground = :white), "in ", Crayon(foreground = :yellow), "$func_name", Crayon(foreground = :blue), "$father_type_vec ", Crayon(foreground = :white), "is not concrete.")
            elseif(father_type_vec != nothing)
                pprintln(Crayon(foreground = :magenta), "| WARNING: ", Crayon(foreground = :white), "Type ", Crayon(foreground = :blue), "$type_to_analyze ", Crayon(foreground = :white), "in ", Crayon(foreground = :blue), "$father_type_vec ", Crayon(foreground = :white), "is not concrete.")
            else
                println(Crayon(foreground = :magenta), "| WARNING: ", Crayon(foreground = :white), "Type ", Crayon(foreground = :blue), "$type_to_analyze ", Crayon(foreground = :white), "is not concrete.")
            end

            return
        end
    end

    if(isa(type_to_analyze, UnionAll))
        println(Crayon(foreground = :magenta), "| WARNING: ", Crayon(foreground = :white), "Type ", Crayon(foreground = :blue), "$type_to_analyze ", Crayon(foreground = :white), "is not concrete. Perhaps it hasn't been parametrized correctly.")
        return
    end

    if(isa(type_to_analyze, Union))
        println(Crayon(foreground = :magenta), "| WARNING: ", Crayon(foreground = :blue), "$type_to_analyze ", Crayon(foreground = :white), "will generate non-specialized code.")

        #Find inner types in the Union anyway
        find_unstable_type_recursive(type_to_analyze.a, type_to_analyze)
        find_unstable_type_recursive(type_to_analyze.b, type_to_analyze)
    end

end

function find_compilable_methods_recursive(f, types_tuple, method_dict)

    #Print out
    println(Crayon(foreground = :white), "|\n| Snooping ", Crayon(foreground = :yellow), "$f", Crayon(foreground = :blue), "$types_tuple", Crayon(foreground = :white), "...")

    #################################
    #Checks for constructor functions

    if(isa(f, DataType))
        
        #Ignore if analyzed DataType is a subtype of Exception
        if(f.super != Exception)
            if(!f.isconcretetype)
                println(Crayon(foreground = :magenta), "| WARNING: ", Crayon(foreground = :white), "Type ", Crayon(foreground = :blue), "$f", Crayon(foreground = :white), " is not concrete.")
            end

            for type_of_field in f.types
                if(isa(type_of_field, Union))
                    println(Crayon(foreground = :magenta), "| WARNING: ", Crayon(foreground = :white), "Type ", Crayon(foreground = :blue), "$type_of_field ", Crayon(foreground = :white), "in ", Crayon(foreground = :yellow), "$f ", Crayon(foreground = :white), "is not concrete.")
                end

                if(isa(type_of_field, UnionAll))
                    println(Crayon(foreground = :magenta), "| WARNING: ", Crayon(foreground = :white), "Type ", Crayon(foreground = :blue), "$type_of_field ", Crayon(foreground = :white), "in ", Crayon(foreground = :yellow), "$f ", Crayon(foreground = :white), "is not concrete. Perhaps it hasn't been parametrized correctly.")
                end

                if(!type_of_field.isconcretetype)
                    println(Crayon(foreground = :magenta), "| WARNING: ", Crayon(foreground = :white), "Type ", Crayon(foreground = :blue), "$type_of_field ", Crayon(foreground = :white), "in ", Crayon(foreground = :yellow), "$f ", Crayon(foreground = :white), "is not concrete.")
                end
            end
        end

    end

    if(isa(f, Union))
        println(Crayon(foreground = :magenta), "| WARNING: ", Crayon(foreground = :white), "Type ", Crayon(foreground = :blue), "$f", Crayon(foreground = :white), " is not concrete.")
    end

    if(isa(f, UnionAll))
        println(Crayon(foreground = :magenta), "| WARNING: ", Crayon(foreground = :white), "Type ", Crayon(foreground = :blue), "$f", Crayon(foreground = :white), " is not concrete. Perhaps it hasn't been parametrized correctly.")
    end
    #################################

    #Types in the arguments tuple to function
    for type in types_tuple
        find_unstable_type_recursive(type, types_tuple, f)
    end

    #Get the full typed graph for the function
    code_typed_content = code_typed(f, types_tuple)

    if(length(code_typed_content) != 1)
        println(Crayon(foreground = :red), "| ERROR: ", Crayon(foreground = :yellow), "$f", Crayon(foreground = :blue), "$types_tuple ", Crayon(foreground = :white), "is not a specialized function - it has $(length(code_typed_content)) methods.")
        return
    end
    
    code_info_typed = code_typed_content[1].first
    
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
            #If val of the Core.PiNode is not a Core.SSAValue, eval and get the type. Otherwise, the type will be the one of the ssavalues array.
            if(!isa(code_line.val, Core.SSAValue))
                type_of_line = typeof(eval(code_line))
                code_ssavaluetypes[line_counter] = type_of_line
            end

        elseif(isa(code_line, Expr))
            
            #Invoke calls (:invoke)
            if(code_line.head == :invoke)
                invoke_call = code_line
                
                method_instance = invoke_call.args[1]
                #println(method_instance)

                method_instance_name = method_instance.def.name
                #println(method_instance_name)

                method_instance_definition = invoke_call.args[2]

                #If method instance definition is a Core.Slotnumber, and the slotnumber is called "self", it means the invoke function to call has the same name as the top called function.
                if(isa(method_instance_definition, Core.SlotNumber))
                    if(code_info_typed.slotnames[method_instance_definition.id] == Symbol("#self#"))
                        method_instance_definition = f
                    end
                end
                #println(method_instance_definition)

                method_instance_args = method_instance.specTypes.parameters[2:end] #Ignore first one, which is the function name
                #println(method_instance_args)

                method_instance_args_tuple = tuple(method_instance_args...) #svec -> Tuple
                #println(method_instance_args_tuple)

                #Sometimes the graph might have a Core.SSAValue representing which function to invoke. I need to retrieve it from the graph first. (See code_typed(LinearAlgebra.det(Array{Float64, 2},)))
                if(isa(method_instance_definition, Core.SSAValue))
                    method_instance_definition = code_line_by_line[method_instance_definition.id]
                    #println(method_instance_definition)
                end

                invoke_method_added = add_to_method_dict(method_dict, method_instance_definition, method_instance_args_tuple)
                if(!invoke_method_added)
                    continue
                end
                #println(method_dict)
                
                #eval(:(Main.code_warntype($method_instance_name, $method_instance_args_tuple)))
                
                #This will check if the sub invoke calls give type errors. It it does, skip the method entirely.
                try
                    eval(:(find_compilable_methods_recursive($method_instance_definition, $method_instance_args_tuple, $method_dict))) #need to wrap in expr because the "method_instance_name" is a Symbol
                catch exception
                    println(Crayon(foreground = :red), "| EXCEPTION DETECTED for $method_instance_definition: ", Crayon(foreground = :white), exception) 
                    continue
                end

            #Function calls (:call)
            elseif(code_line.head == :call)
                
                call_function_name = code_line.args[1]

                #Sometimes the graph might have a Core.SSAValue representing which function to invoke. Retrieve the actual name of the function from the line by line table, using the id of the Core.SSAValue
                if(isa(call_function_name, Core.SSAValue))
                    call_function_name = code_line_by_line[call_function_name.id]
                    #println(call_function_name)
                end

                eval_call_function_name = eval(:($call_function_name))

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

                #Find the SSAValues inside the code for this specific :call
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
                        eval(:(find_compilable_methods_recursive($call_function_name, $call_tuple_types, $method_dict))) #need to wrap in expr because the "method_instance_name" is a Symbol
                    catch exception
                        println(Crayon(foreground = :red), "| EXCEPTION DETECTED for $method_instance_definition: ", Crayon(foreground = :white), exception)
                        continue
                    end
                end

            #Constructor calls (:new)
            elseif(code_line.head == :new)
                constructor_call = code_line
                constructor_type = eval(:($(constructor_call.args[1]))) #This is a DataType

                typeassert(constructor_type, DataType)

                #Actual types of the fields of constructor_type 
                constructor_args = constructor_type.types

                #Eventual "baked in" stuff. Like literal Strings, etc. It mostly will contain Core.SSAValues, or references to variables.
                constructor_args_code = constructor_call.args[2:end]

                println(Crayon(foreground = :white), "|\n| Snooping constructor of ", Crayon(foreground = :yellow), "$constructor_type", Crayon(foreground = :blue), "$(tuple(constructor_args...))", Crayon(foreground = :white), "...")

                #Empty vector to fill if some of the types in constructor_args_code are concrete subtypes of constructor_args
                constructor_args_new_vec = Vector{Any}(undef, length(constructor_args))

                #println("$constructor_type, $(length(constructor_args_code))")

                #Special case for one field with AbstractString, precompile for String. It's the case for most ErrorException(), OverflowError... etc...
                if(length(constructor_args) == 1 && eval(constructor_args[1]) == AbstractString)
                    constructor_args_new_vec[1] = String
                    println(Crayon(foreground = :green), "| FOUND ", Crayon(foreground = :blue), "AbstractString ", Crayon(foreground = :white), "as only argument to ", Crayon(foreground = :yellow),  "$constructor_type", Crayon(foreground = :white),  "'s constructor. Using concrete Type ", Crayon(foreground = :blue), "String", Crayon(foreground = :white), ".")
                else
                    constructor_counter = 1

                    for type_of_field in constructor_args

                        if(isa(type_of_field, Union))
                            println(Crayon(foreground = :magenta), "| WARNING: ", Crayon(foreground = :white), "Field ", Crayon(foreground = :blue), "$type_of_field ",  Crayon(foreground = :white), "in ",  Crayon(foreground = :yellow), "$constructor_type ",  Crayon(foreground = :white), "is not concrete.")

                        elseif(isa(type_of_field, UnionAll))
                            println(Crayon(foreground = :magenta), "| WARNING: ", Crayon(foreground = :white), "Field ",  Crayon(foreground = :blue), "$type_of_field ",  Crayon(foreground = :white), "in ",  Crayon(foreground = :yellow), "$constructor_type ",  Crayon(foreground = :white), "is not concrete. Perhaps it hasn't been parametrized correctly.")
                        
                        elseif(!isconcretetype(type_of_field))
                            println(Crayon(foreground = :magenta), "| WARNING: ", Crayon(foreground = :white), "Field ", Crayon(foreground = :blue), "$type_of_field ",  Crayon(foreground = :white), "in ",  Crayon(foreground = :yellow), "$constructor_type ",  Crayon(foreground = :white), "is not concrete.")
                        end

                        #First of all, just fill the empty vector with the standard tuple() values for this constructor
                        constructor_args_new_vec[constructor_counter] = type_of_field

                        #First, check if there actually is stuff to look for. If length is 0, nothing is baked in.
                        if(length(constructor_args_code) > 1)

                            #Check if any type in the args to the :new Expr are baked in (mostly, String values)
                            type_in_constructor_args_code = typeof(constructor_args_code[constructor_counter])

                            #First check if the argument is directly inserted as subtype in the graph (as the case for String(s) in AbstractString(s) functions, check code_typed(rand, (Int64, Int64) and its AssertionError fuction))
                            if(isconcretetype(type_in_constructor_args_code) && isa(type_of_field, Type) && type_of_field != Any && isabstracttype(type_of_field))
                                if(type_in_constructor_args_code <: type_of_field)
                                    constructor_args_new_vec[constructor_counter] = type_in_constructor_args_code
                                    println(Crayon(foreground = :green), "| FOUND ", Crayon(foreground = :blue), "$type_in_constructor_args_code ", Crayon(foreground = :white), "as concrete subtype of ", Crayon(foreground = :blue),  "$type_of_field. ", Crayon(foreground = :white),  "Using ", Crayon(foreground = :blue), "$type_in_constructor_args_code." )
                                end
                            end
                        end

                        constructor_counter = constructor_counter + 1
                    end
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

    deep_precompile(myStruct{Float64, Int64}, (Float64, Int64))

    deep_precompile(test_calc, (myStruct{Float64, Int64}, ))

    #deep_precompile(myUnstableStruct, (Float64, Int64))

    #find_compilable_methods(myStruct{Float64, Int64}, (Float64, Int64))

    #The resulting fields in myStruct{Float64, Int64} are seen as concrete.
    #find_compilable_methods(test_calc, (myStruct{Float64, Int64}, ))

    #find_compilable_methods(myUnstableStruct, (Float64, Int64))
end

#test_warntypes()

#test_precompiler()

end

#MAIN

#using Plots

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


function test_precompiler()
    Precompiler.deep_precompile(func_with_everything, ())
end

test_precompiler()

@time func_with_everything()

@time func_with_everything()