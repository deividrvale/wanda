Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| CN  
| CO.
Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.


Definition N := 
Base CN.
Definition O := 
Base CO.



Inductive fun_symbols := 
| Tlim  
| Tplus  
| Ts  
| Tz  
| TAP1.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tlim  =>  (N ⟶ O) ⟶ O
  | Tplus  =>  O ⟶ O ⟶ O
  | Ts  =>  O ⟶ O
  | Tz  =>  O
  | TAP1 => (N ⟶ O) ⟶ N ⟶ O
end.
Definition lim {C} : tm fn_arity C _ := 
BaseTm Tlim.
Definition plus {C} : tm fn_arity C _ := 
BaseTm Tplus.
Definition s {C} : tm fn_arity C _ := 
BaseTm Ts.
Definition z {C} : tm fn_arity C _ := 
BaseTm Tz.
Definition AP1 {C} : tm fn_arity C _ := 
BaseTm TAP1.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, ∙) _
    (plus · z ·  V 0)
     V 0.
Program Definition rule_1 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (plus · (s ·  V 0) ·  V 1)
    (s · (plus ·  V 0 ·  V 1)).
Program Definition rule_2 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (plus · (lim · (λ AP1 ·  V 1 ·  V 0)) ·  V 1)
    (lim · (λ plus · (AP1 ·  V 1 ·  V 0) ·  V 2)).
Program Definition rule_3 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (AP1 ·  V 0 ·  V 1)
    ( V 0 ·  V 1).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tlim  => 
 λP
(to_Poly (P_const 3))
| Tplus  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y0 * y1 + P_const 3 * y1))
| Ts  => 
 λP
(to_Poly (P_const 3))
| Tz  => 
 (to_Poly (P_const 3))
| TAP1 => 
λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * (G0 ·P (P_const 0)) + P_const 3 * (G0 ·P (y1))))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
