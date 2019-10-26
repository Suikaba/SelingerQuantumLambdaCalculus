type ('a, 'b) t

exception Not_bound

val empty : ('a, 'b) t
val extend : ('a, 'b) t -> 'a -> 'b -> ('a, 'b) t
val lookup : ('a, 'b) t -> 'a -> 'b
val map : ('a, 'b) t -> ('b -> 'c) -> ('a, 'c) t
val domain : ('a, 'b) t -> 'a list
