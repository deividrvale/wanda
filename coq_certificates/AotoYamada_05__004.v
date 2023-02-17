Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| Ca  
| Cb.
Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.


Definition a := 
Base Ca.
Definition b := 
Base Cb.



Inductive fun_symbols := 
| Tcons  
| Tnil  
| Tplus  
| Ts  
| Tsumwith  
| Tzero.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tcons  =>  a ⟶ b ⟶ b
  | Tnil  =>  b
  | Tplus  =>  b ⟶ b ⟶ b
  | Ts  =>  b ⟶ b
  | Tsumwith  =>  (a ⟶ b) ⟶ b ⟶ b
  | Tzero => b
end.
Definition cons {C} : tm fn_arity C _ := 
BaseTm Tcons.
Definition nil {C} : tm fn_arity C _ := 
BaseTm Tnil.
Definition plus {C} : tm fn_arity C _ := 
BaseTm Tplus.
Definition s {C} : tm fn_arity C _ := 
BaseTm Ts.
Definition sumwith {C} : tm fn_arity C _ := 
BaseTm Tsumwith.
Definition zero {C} : tm fn_arity C _ := 
BaseTm Tzero.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, ∙) _
    (plus · zero ·  V 0)
     V 0.
Program Definition rule_1 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (plus · (s ·  V 0) ·  V 1)
    (s · (plus ·  V 0 ·  V 1)).
Program Definition rule_2 := 
    make_rewrite
    (_ ,, ∙) _
    (sumwith ·  V 0 · nil)
    nil.
Program Definition rule_3 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (sumwith ·  V 0 · (cons ·  V 1 ·  V 2))
    (plus · ( V 0 ·  V 1) · (sumwith ·  V 0 ·  V 2)).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tcons  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y0 * y1 + P_const 3 * y1))
| Tnil  => 
 (to_Poly (P_const 3))
| Tplus  => 
 λP let y0 := P_var (Vs Vz) in
λP
(to_Poly (y0))
| Ts  => 
 λP
(to_Poly (P_const 3))
| Tsumwith  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 2 * y1 + P_const 2 * (G0 ·P (y1)) + P_const 3 * y1 * (G0 ·P (y1))))
| Tzero => 
(to_Poly (P_const 3))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
