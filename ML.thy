(*<*)
theory "ML"
  imports Pure
begin
(*>*)

ML \<open>
structure Nat : sig
  type nat
  val init : int -> nat
  val get : nat -> int
end = struct
  exception Negative of int
  abstype nat = Nat of int with
    fun init v = if v < 0 then raise Negative v else Nat v
    fun get (Nat v) = v
  end
end
\<close>

ML \<open>Nat.init 1; Nat.init ~1\<close>

ML \<open>
structure Nat :> sig
  type nat \<comment> \<open>The type is treated as fully abstract outside the module\<close>
  val init : int -> nat
  val get : nat -> int
end = struct
  exception Negative of int
  type nat = int
  fun init v = if v < 0 then raise Negative v else v
  fun get v = v
end
\<close>
ML \<open>Nat.init 1\<close> \<comment> \<open>Note that the actual value is not printed\<close>

ML \<open>@{apply 4(2)}\<close>
ML \<open>fn f => fn (a, b, c, d) => (a, f b, c, d)\<close>

ML \<open>fn f => @{apply 3(3)} (@{apply 3(2)} f)\<close>
ML \<open>@{apply 3(3)} o @{apply 3(2)}\<close>
ML \<open>@{apply 3(2)} #> @{apply 3(3)}\<close>

ML \<open>(@{apply 3(3)} o @{apply 3(2)}) (\<^print> o curry op + 1) (1, "2", (3.0, 4, "5"))\<close>

(*<*)
end
(*>*)
