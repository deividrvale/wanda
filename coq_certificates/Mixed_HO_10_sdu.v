Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| Ca  
| Cb  
| Cu.
Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.


Definition a := 
Base Ca.
Definition b := 
Base Cb.
Definition u := 
Base Cu.



Inductive fun_symbols := 
| Tcasea  
| Tcaseb  
| Tcaseu  
| Tinl  
| Tinr  
| TAP1  
| TAP2  
| TAP3.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tcasea  =>  u ⟶ (a ⟶ a) ⟶ (b ⟶ a) ⟶ a
  | Tcaseb  =>  u ⟶ (a ⟶ b) ⟶ (b ⟶ b) ⟶ b
  | Tcaseu  =>  u ⟶ (a ⟶ u) ⟶ (b ⟶ u) ⟶ u
  | Tinl  =>  a ⟶ u
  | Tinr  =>  b ⟶ u
  | TAP1  =>  (u ⟶ a) ⟶ u ⟶ a
  | TAP2  =>  (u ⟶ b) ⟶ u ⟶ b
  | TAP3 => (u ⟶ u) ⟶ u ⟶ u
end.
Definition casea {C} : tm fn_arity C _ := 
BaseTm Tcasea.
Definition caseb {C} : tm fn_arity C _ := 
BaseTm Tcaseb.
Definition caseu {C} : tm fn_arity C _ := 
BaseTm Tcaseu.
Definition inl {C} : tm fn_arity C _ := 
BaseTm Tinl.
Definition inr {C} : tm fn_arity C _ := 
BaseTm Tinr.
Definition AP1 {C} : tm fn_arity C _ := 
BaseTm TAP1.
Definition AP2 {C} : tm fn_arity C _ := 
BaseTm TAP2.
Definition AP3 {C} : tm fn_arity C _ := 
BaseTm TAP3.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (casea · (inl ·  V 0) ·  V 1 ·  V 2)
    ( V 1 ·  V 0).
Program Definition rule_1 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (casea · (inr ·  V 0) ·  V 1 ·  V 2)
    ( V 2 ·  V 0).
Program Definition rule_2 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (casea ·  V 0 · (λ AP1 ·  V 2 · (inl ·  V 0)) · (λ AP1 ·  V 2 · (inr ·  V 0)))
    (AP1 ·  V 1 ·  V 0).
Program Definition rule_3 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (caseb · (inl ·  V 0) ·  V 1 ·  V 2)
    ( V 1 ·  V 0).
Program Definition rule_4 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (caseb · (inr ·  V 0) ·  V 1 ·  V 2)
    ( V 2 ·  V 0).
Program Definition rule_5 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (caseb ·  V 0 · (λ AP2 ·  V 2 · (inl ·  V 0)) · (λ AP2 ·  V 2 · (inr ·  V 0)))
    (AP2 ·  V 1 ·  V 0).
Program Definition rule_6 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (caseu · (inl ·  V 0) ·  V 1 ·  V 2)
    ( V 1 ·  V 0).
Program Definition rule_7 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (caseu · (inr ·  V 0) ·  V 1 ·  V 2)
    ( V 2 ·  V 0).
Program Definition rule_8 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (caseu ·  V 0 · (λ AP3 ·  V 2 · (inl ·  V 0)) · (λ AP3 ·  V 2 · (inr ·  V 0)))
    (AP3 ·  V 1 ·  V 0).
Program Definition rule_9 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (AP1 ·  V 0 ·  V 1)
    ( V 0 ·  V 1).
Program Definition rule_10 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (AP2 ·  V 0 ·  V 1)
    ( V 0 ·  V 1).
Program Definition rule_11 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (AP3 ·  V 0 ·  V 1)
    ( V 0 ·  V 1).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: rule_4 :: rule_5 :: rule_6 :: rule_7 :: rule_8 :: rule_9 :: rule_10 :: rule_11 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tcasea  => 
 λP let y0 := P_var (Vs (Vs Vz)) in
λP let G1 := P_var (Vs Vz) in
λP let G2 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y0 * (G1 ·P (y0)) + P_const 3 * y0 * (G2 ·P (y0)) + P_const 3 * (G1 ·P (P_const 0)) + P_const 3 * (G1 ·P (y0)) + P_const 3 * (G2 ·P (P_const 0)) + P_const 3 * (G2 ·P (y0))))
| Tcaseb  => 
 λP let y0 := P_var (Vs (Vs Vz)) in
λP let G1 := P_var (Vs Vz) in
λP let G2 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y0 * (G1 ·P (y0)) + P_const 3 * y0 * (G2 ·P (y0)) + P_const 3 * (G1 ·P (P_const 0)) + P_const 3 * (G1 ·P (y0)) + P_const 3 * (G2 ·P (P_const 0)) + P_const 3 * (G2 ·P (y0))))
| Tcaseu  => 
 λP let y0 := P_var (Vs (Vs Vz)) in
λP let G1 := P_var (Vs Vz) in
λP let G2 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y0 * (G1 ·P (y0)) + P_const 3 * y0 * (G2 ·P (y0)) + P_const 3 * (G1 ·P (P_const 0)) + P_const 3 * (G1 ·P (y0)) + P_const 3 * (G2 ·P (P_const 0)) + P_const 3 * (G2 ·P (y0))))
| Tinl  => 
 λP let y0 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0))
| Tinr  => 
 λP let y0 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0))
| TAP1  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 2 * (G0 ·P (y1)) + P_const 3 * (G0 ·P (P_const 0))))
| TAP2  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + (G0 ·P (y1)) + P_const 3 * (G0 ·P (P_const 0))))
| TAP3 => 
λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + (G0 ·P (y1)) + P_const 3 * (G0 ·P (P_const 0))))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
