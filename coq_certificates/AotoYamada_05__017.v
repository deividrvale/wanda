Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| Ca  
| Cb  
| Cc.
Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.


Definition a := 
Base Ca.
Definition b := 
Base Cb.
Definition c := 
Base Cc.



Inductive fun_symbols := 
| Tuncurry.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tuncurry => (a ⟶ b ⟶ c) ⟶ a ⟶ b ⟶ c
end.
Definition uncurry {C} : tm fn_arity C _ := 
BaseTm Tuncurry.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (uncurry ·  V 0 ·  V 1 ·  V 2)
    ( V 0 ·  V 1 ·  V 2).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tuncurry => 
λP let G0 := P_var (Vs (Vs Vz)) in
λP let y1 := P_var (Vs Vz) in
λP let y2 := P_var Vz in
(to_Poly (P_const 2 + P_const 3 * ((G0 ·P (P_const 0)) ·P (P_const 0)) + P_const 3 * ((G0 ·P (y1)) ·P (y1)) + P_const 3 * ((G0 ·P (y1)) ·P (y2)) + P_const 3 * ((G0 ·P (y2)) ·P (y1)) + P_const 3 * ((G0 ·P (y2)) ·P (y2))))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
