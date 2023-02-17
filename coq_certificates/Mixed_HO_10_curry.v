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
| Ta  
| Tf  
| TAP1.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Ta  =>  N
  | Tf  =>  N ⟶ N
  | TAP1 => (N ⟶ N) ⟶ N ⟶ N
end.
Definition a {C} : tm fn_arity C _ := 
BaseTm Ta.
Definition f {C} : tm fn_arity C _ := 
BaseTm Tf.
Definition AP1 {C} : tm fn_arity C _ := 
BaseTm TAP1.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, ∙) _
    (AP1 ·  V 0 · a)
    (f · a).
Program Definition rule_1 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (AP1 ·  V 0 ·  V 1)
    ( V 0 ·  V 1).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Ta  => 
 (to_Poly (P_const 0))
| Tf  => 
 λP
(to_Poly (P_const 0))
| TAP1 => 
λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y1 + P_const 3 * (G0 ·P (P_const 0)) + P_const 3 * (G0 ·P (y1))))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
