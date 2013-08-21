signature IMPROVE_TWO_STRUCTS =
sig
    include SHRINK
end

signature IMPROVE_TWO =
sig
    include IMPROVE_TWO_STRUCTS

    val improve: Program.t -> Program.t
end
