Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| CA  
| CN.
Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.


Definition A := 
Base CA.
Definition N := 
Base CN.



Inductive fun_symbols := 
| TNIL  
| TIN  
| Tnew  
| Tout  
| Tsum  
| Ttau  
| TAP1  
| TAP2.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | TNIL  =>  A
  | TIN  =>  N ⟶ (N ⟶ A) ⟶ A
  | Tnew  =>  (N ⟶ A) ⟶ A
  | Tout  =>  N ⟶ N ⟶ A ⟶ A
  | Tsum  =>  A ⟶ A ⟶ A
  | Ttau  =>  A ⟶ A
  | TAP1  =>  (N ⟶ A) ⟶ N ⟶ A
  | TAP2 => (N ⟶ N ⟶ A) ⟶ N ⟶ N ⟶ A
end.
Definition NIL {C} : tm fn_arity C _ := 
BaseTm TNIL.
Definition IN {C} : tm fn_arity C _ := 
BaseTm TIN.
Definition new {C} : tm fn_arity C _ := 
BaseTm Tnew.
Definition out {C} : tm fn_arity C _ := 
BaseTm Tout.
Definition sum {C} : tm fn_arity C _ := 
BaseTm Tsum.
Definition tau {C} : tm fn_arity C _ := 
BaseTm Ttau.
Definition AP1 {C} : tm fn_arity C _ := 
BaseTm TAP1.
Definition AP2 {C} : tm fn_arity C _ := 
BaseTm TAP2.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, ∙) _
    (sum · NIL ·  V 0)
     V 0.
Program Definition rule_1 := 
    make_rewrite
    (_ ,, ∙) _
    (new · (λ  V 1))
     V 0.
Program Definition rule_2 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (new · (λ sum · (AP1 ·  V 1 ·  V 0) · (AP1 ·  V 2 ·  V 0)))
    (sum · (new · (λ AP1 ·  V 1 ·  V 0)) · (new · (λ AP1 ·  V 2 ·  V 0))).
Program Definition rule_3 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (new · (λ out ·  V 0 ·  V 1 · (AP1 ·  V 2 ·  V 0)))
    NIL.
Program Definition rule_4 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (new · (λ out ·  V 1 ·  V 2 · (AP1 ·  V 3 ·  V 0)))
    (out ·  V 0 ·  V 1 · (new · (λ AP1 ·  V 3 ·  V 0))).
Program Definition rule_5 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (new · (λ IN ·  V 1 · (λ AP1 · (AP2 ·  V 3 ·  V 1) ·  V 0)))
    (IN ·  V 0 · (λ new · (λ AP1 · (AP2 ·  V 3 ·  V 0) ·  V 1))).
Program Definition rule_6 := 
    make_rewrite
    (_ ,, ∙) _
    (new · (λ tau · (AP1 ·  V 1 ·  V 0)))
    (tau · (new · (λ AP1 ·  V 1 ·  V 0))).
Program Definition rule_7 := 
    make_rewrite
    (_ ,, ∙) _
    (new · (λ IN ·  V 0 · (λ AP1 · (AP2 ·  V 2 ·  V 1) ·  V 0)))
    NIL.
Program Definition rule_8 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (AP1 ·  V 0 ·  V 1)
    ( V 0 ·  V 1).
Program Definition rule_9 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (AP2 ·  V 0 ·  V 1)
    ( V 0 ·  V 1).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: rule_4 :: rule_5 :: rule_6 :: rule_7 :: rule_8 :: rule_9 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| TNIL  => 
 (to_Poly (P_const 0))
| TIN  => 
 λP let y0 := P_var (Vs Vz) in
λP
(to_Poly (P_const 3 + P_const 3 * y0))
| Tnew  => 
 λP let G0 := P_var Vz in
(to_Poly (P_const 1 + P_const 3 * (G0 ·P (P_const 0))))
| Tout  => 
 λP let y0 := P_var (Vs (Vs Vz)) in
λP let y1 := P_var (Vs Vz) in
λP
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y1))
| Tsum  => 
 λP
λP
(to_Poly (P_const 3))
| Ttau  => 
 λP
(to_Poly (P_const 3))
| TAP1  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * (G0 ·P (y1))))
| TAP2 => 
λP let G0 := P_var (Vs (Vs Vz)) in
λP let y1 := P_var (Vs Vz) in
λP let y2 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * ((G0 ·P (P_const 0)) ·P (P_const 0)) + P_const 3 * ((G0 ·P (y1)) ·P (y1)) + P_const 3 * ((G0 ·P (y1)) ·P (y2)) + P_const 3 * ((G0 ·P (y2)) ·P (y1)) + P_const 3 * ((G0 ·P (y2)) ·P (y2))))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
