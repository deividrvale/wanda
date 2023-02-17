Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| Cform.
Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.


Definition form := 
Base Cform.



Inductive fun_symbols := 
| Tand  
| TEXISTS  
| TFORALL  
| Tnot  
| Tor  
| TAP1.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tand  =>  form ⟶ form ⟶ form
  | TEXISTS  =>  (form ⟶ form) ⟶ form
  | TFORALL  =>  (form ⟶ form) ⟶ form
  | Tnot  =>  form ⟶ form
  | Tor  =>  form ⟶ form ⟶ form
  | TAP1 => (form ⟶ form) ⟶ form ⟶ form
end.
Definition and {C} : tm fn_arity C _ := 
BaseTm Tand.
Definition EXISTS {C} : tm fn_arity C _ := 
BaseTm TEXISTS.
Definition FORALL {C} : tm fn_arity C _ := 
BaseTm TFORALL.
Definition not {C} : tm fn_arity C _ := 
BaseTm Tnot.
Definition or {C} : tm fn_arity C _ := 
BaseTm Tor.
Definition AP1 {C} : tm fn_arity C _ := 
BaseTm TAP1.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (and ·  V 0 · (FORALL · (λ AP1 ·  V 2 ·  V 0)))
    (FORALL · (λ and ·  V 1 · (AP1 ·  V 2 ·  V 0))).
Program Definition rule_1 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (or ·  V 0 · (FORALL · (λ AP1 ·  V 2 ·  V 0)))
    (FORALL · (λ or ·  V 1 · (AP1 ·  V 2 ·  V 0))).
Program Definition rule_2 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (and · (FORALL · (λ AP1 ·  V 1 ·  V 0)) ·  V 1)
    (FORALL · (λ and · (AP1 ·  V 1 ·  V 0) ·  V 2)).
Program Definition rule_3 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (or · (FORALL · (λ AP1 ·  V 1 ·  V 0)) ·  V 1)
    (FORALL · (λ or · (AP1 ·  V 1 ·  V 0) ·  V 2)).
Program Definition rule_4 := 
    make_rewrite
    (_ ,, ∙) _
    (not · (FORALL · (λ AP1 ·  V 1 ·  V 0)))
    (EXISTS · (λ not · (AP1 ·  V 1 ·  V 0))).
Program Definition rule_5 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (and ·  V 0 · (EXISTS · (λ AP1 ·  V 2 ·  V 0)))
    (EXISTS · (λ and ·  V 1 · (AP1 ·  V 2 ·  V 0))).
Program Definition rule_6 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (or ·  V 0 · (EXISTS · (λ AP1 ·  V 2 ·  V 0)))
    (EXISTS · (λ or ·  V 1 · (AP1 ·  V 2 ·  V 0))).
Program Definition rule_7 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (and · (EXISTS · (λ AP1 ·  V 1 ·  V 0)) ·  V 1)
    (EXISTS · (λ and · (AP1 ·  V 1 ·  V 0) ·  V 2)).
Program Definition rule_8 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (or · (EXISTS · (λ AP1 ·  V 1 ·  V 0)) ·  V 1)
    (EXISTS · (λ or · (AP1 ·  V 1 ·  V 0) ·  V 2)).
Program Definition rule_9 := 
    make_rewrite
    (_ ,, ∙) _
    (not · (EXISTS · (λ AP1 ·  V 1 ·  V 0)))
    (FORALL · (λ not · (AP1 ·  V 1 ·  V 0))).
Program Definition rule_10 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (AP1 ·  V 0 ·  V 1)
    ( V 0 ·  V 1).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: rule_4 :: rule_5 :: rule_6 :: rule_7 :: rule_8 :: rule_9 :: rule_10 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tand  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (y0 + y1 + P_const 3 * y0 * y1))
| TEXISTS  => 
 λP let G0 := P_var Vz in
(to_Poly (P_const 2 + P_const 3 * (G0 ·P (P_const 0))))
| TFORALL  => 
 λP let G0 := P_var Vz in
(to_Poly (P_const 2 + P_const 3 * (G0 ·P (P_const 0))))
| Tnot  => 
 λP let y0 := P_var Vz in
(to_Poly (P_const 2 * y0))
| Tor  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (y0 + y1 + P_const 3 * y0 * y1))
| TAP1 => 
λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 2 + P_const 3 * (G0 ·P (P_const 0)) + P_const 3 * (G0 ·P (y1))))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
