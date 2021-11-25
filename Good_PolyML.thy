theory Good_PolyML
  imports Main
begin
\<comment> \<open>An actual demonstration that PolyML is pretty good at common optimizations!\<close>
ML \<open>
  datatype inlined =
    I1 of int * string
  | I2 of int * bool * bool

  datatype extruded =
    E1 of (int * string)
  | E2 of (int * bool * bool)

 datatype wrapped = Wrap of extruded

  datatype stupid =
    S1 of (int * string)
  | S2 of ((int * bool) * bool)

 fun random_int () = Random.random_range 0 (FixedInt.maxInt |> the |> FixedInt.toInt)
 fun random_bool () = Random.random_range 0 1 = 0

 fun gen_inlined 0 l = l
   | gen_inlined n l =
       gen_inlined
         (n - 1)
         ((case Random.random_range 0 1 of
             0 => I1 (random_int (), random_int () |> string_of_int)
           | 1 => I2 (random_int (), random_bool(), random_bool ())) :: l)

 fun gen_extruded 0 l = l
   | gen_extruded n l =
       gen_extruded
         (n - 1)
         ((case Random.random_range 0 1 of
             0 => E1 (random_int (), random_int () |> string_of_int)
           | 1 => E2 (random_int (), random_bool(), random_bool ())) :: l)

  fun gen_wrapped 0 l = l
    | gen_wrapped n l =
       gen_wrapped
         (n - 1)
         (Wrap (case Random.random_range 0 1 of
             0 => E1 (random_int (), random_int () |> string_of_int)
           | 1 => E2 (random_int (), random_bool(), random_bool ())) :: l)

 fun gen_stupid 0 l = l
   | gen_stupid n l =
       gen_stupid
         (n - 1)
         ((case Random.random_range 0 1 of
             0 => S1 (random_int (), random_int () |> string_of_int)
           | 1 => S2 ((random_int (), random_bool()), random_bool ())) :: l)

  fun ord_inlined (I1 a1, I1 a2) = prod_ord int_ord fast_string_ord (a1, a2)
    | ord_inlined (I1 _, I2 _) = LESS
    | ord_inlined (I2 _, I1 _) = GREATER
    | ord_inlined (I2 a1, I2 a2) =
        (a1, a2) |> (prod_ord int_ord bool_ord o apply2 (Nitpick_Util.pairf #1 #2) ||| bool_ord o apply2 #3)

  fun ord_extruded (E1 a1, E1 a2) = prod_ord int_ord fast_string_ord (a1, a2)
    | ord_extruded (E1 _, E2 _) = LESS
    | ord_extruded (E2 _, E1 _) = GREATER
    | ord_extruded (E2 a1, E2 a2) =
        (a1, a2) |> (prod_ord int_ord bool_ord o apply2 (Nitpick_Util.pairf #1 #2) ||| bool_ord o apply2 #3)

  fun ord_wrapped (Wrap e1, Wrap e2)= ord_extruded (e1, e2)

  fun ord_stupid (S1 a1, S1 a2) = prod_ord int_ord fast_string_ord (a1, a2)
    | ord_stupid (S1 _, S2 _) = LESS
    | ord_stupid (S2 _, S1 _) = GREATER
    | ord_stupid (S2 a1, S2 a2) = (a1, a2) |> (prod_ord int_ord bool_ord o apply2 #1 ||| bool_ord o apply2 #2)

  fun time f = Timing.start () |> pair (f ()) ||> Timing.result

  val pp = time ML_Heap.full_gc
  val x = time (fn () =>  gen_inlined 900000 [] |> sort ord_inlined) |> \<^print> |> ignore
  val xx = time ML_Heap.full_gc
  val y = time (fn () =>  gen_extruded 900000 [] |> sort ord_extruded) |> \<^print> |> ignore
  val yy = time ML_Heap.full_gc
  val z = time (fn () =>  gen_wrapped 900000 [] |> sort ord_wrapped) |> \<^print> |> ignore
  val zz = time ML_Heap.full_gc
  val u = time (fn () =>  gen_stupid 900000 [] |> sort ord_stupid) |> \<^print> |> ignore
  val uu = time ML_Heap.full_gc
\<close>

end