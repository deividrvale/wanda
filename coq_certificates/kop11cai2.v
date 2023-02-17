Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| Cnat.
Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.


Definition nat := 
Base Cnat.



Inductive fun_symbols := 
| Tpair  
| Tsplit  
| TAP1.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tpair  =>  (nat ⟶ nat) ⟶ nat ⟶ nat
  | Tsplit  =>  nat ⟶ nat
  | TAP1 => (nat ⟶ nat) ⟶ nat ⟶ nat
end.
Definition pair {C} : tm fn_arity C _ := 
BaseTm Tpair.
Definition split {C} : tm fn_arity C _ := 
BaseTm Tsplit.
Definition AP1 {C} : tm fn_arity C _ := 
BaseTm TAP1.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (split · (AP1 ·  V 0 ·  V 1))
    (pair ·  V 0 ·  V 1).
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
| Tpair  => 
 λP
λP
(to_Poly (P_const 0))
| Tsplit  => 
 λP let y0 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0))
| TAP1 => 
λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y1 + P_const 3 * y1 * (G0 ·P (y1)) + P_const 3 * (G0 ·P (P_const 0)) + P_const 3 * (G0 ·P (y1))))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
