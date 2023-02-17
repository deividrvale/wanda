Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| Cdata  
| Cproc.
Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.


Definition data := 
Base Cdata.
Definition proc := 
Base Cproc.



Inductive fun_symbols := 
| Tdelta  
| Tplus  
| Tsigma  
| Ttimes  
| TAP1.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tdelta  =>  proc
  | Tplus  =>  proc ⟶ proc ⟶ proc
  | Tsigma  =>  (data ⟶ proc) ⟶ proc
  | Ttimes  =>  proc ⟶ proc ⟶ proc
  | TAP1 => (data ⟶ proc) ⟶ data ⟶ proc
end.
Definition delta {C} : tm fn_arity C _ := 
BaseTm Tdelta.
Definition plus {C} : tm fn_arity C _ := 
BaseTm Tplus.
Definition sigma {C} : tm fn_arity C _ := 
BaseTm Tsigma.
Definition times {C} : tm fn_arity C _ := 
BaseTm Ttimes.
Definition AP1 {C} : tm fn_arity C _ := 
BaseTm TAP1.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, ∙) _
    (plus ·  V 0 ·  V 0)
     V 0.
Program Definition rule_1 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (times · (plus ·  V 0 ·  V 1) ·  V 2)
    (plus · (times ·  V 0 ·  V 2) · (times ·  V 1 ·  V 2)).
Program Definition rule_2 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (times · (times ·  V 0 ·  V 1) ·  V 2)
    (times ·  V 0 · (times ·  V 1 ·  V 2)).
Program Definition rule_3 := 
    make_rewrite
    (_ ,, ∙) _
    (plus ·  V 0 · delta)
     V 0.
Program Definition rule_4 := 
    make_rewrite
    (_ ,, ∙) _
    (times · delta ·  V 0)
    delta.
Program Definition rule_5 := 
    make_rewrite
    (_ ,, ∙) _
    (sigma · (λ  V 1))
     V 0.
Program Definition rule_6 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (plus · (sigma · (λ AP1 ·  V 1 ·  V 0)) · (AP1 ·  V 0 ·  V 1))
    (sigma · (λ AP1 ·  V 1 ·  V 0)).
Program Definition rule_7 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (sigma · (λ plus · (AP1 ·  V 1 ·  V 0) · (AP1 ·  V 2 ·  V 0)))
    (plus · (sigma · (λ AP1 ·  V 1 ·  V 0)) · (sigma · (λ AP1 ·  V 2 ·  V 0))).
Program Definition rule_8 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (times · (sigma · (λ AP1 ·  V 1 ·  V 0)) ·  V 1)
    (sigma · (λ times · (AP1 ·  V 1 ·  V 0) ·  V 2)).
Program Definition rule_9 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (AP1 ·  V 0 ·  V 1)
    ( V 0 ·  V 1).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: rule_4 :: rule_5 :: rule_6 :: rule_7 :: rule_8 :: rule_9 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tdelta  => 
 (to_Poly (P_const 3))
| Tplus  => 
 λP
λP
(to_Poly (P_const 3))
| Tsigma  => 
 λP let G0 := P_var Vz in
(to_Poly (P_const 2 + P_const 3 * (G0 ·P (P_const 0))))
| Ttimes  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 1 + P_const 2 * y0 * y1 + P_const 3 * y0))
| TAP1 => 
λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 1 + P_const 3 * y1 + (G0 ·P (y1)) + P_const 3 * y1 * (G0 ·P (y1))))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
