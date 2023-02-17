Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| CN.
Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.


Definition N := 
Base CN.



Inductive fun_symbols := 
| Tf  
| Tg  
| Th.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tf  =>  (N ⟶ N) ⟶ N ⟶ N
  | Tg  =>  N ⟶ N
  | Th => N ⟶ N
end.
Definition f {C} : tm fn_arity C _ := 
BaseTm Tf.
Definition g {C} : tm fn_arity C _ := 
BaseTm Tg.
Definition h {C} : tm fn_arity C _ := 
BaseTm Th.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, ∙) _
    (f · g ·  V 0)
    (h ·  V 0).
Program Definition rule_1 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (f ·  V 0 ·  V 1)
    ( V 0 ·  V 1).
Program Definition rule_2 := 
    make_rewrite
    (_ ,, ∙) _
    (h ·  V 0)
    (f · (λ  V 0) ·  V 0).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tf  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 1 + P_const 2 * (G0 ·P (y1)) + P_const 3 * (G0 ·P (P_const 0))))
| Tg  => 
 λP let y0 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0))
| Th => 
λP let y0 := P_var Vz in
(to_Poly (P_const 3 + P_const 2 * y0))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
