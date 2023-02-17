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
| Tadd  
| Tcons  
| Tid  
| Tmap  
| Tnil  
| Ts  
| Tzero.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tadd  =>  a ⟶ a ⟶ a
  | Tcons  =>  b ⟶ c ⟶ c
  | Tid  =>  a ⟶ a
  | Tmap  =>  (b ⟶ b) ⟶ c ⟶ c
  | Tnil  =>  c
  | Ts  =>  a ⟶ a
  | Tzero => a
end.
Definition add {C} : tm fn_arity C _ := 
BaseTm Tadd.
Definition cons {C} : tm fn_arity C _ := 
BaseTm Tcons.
Definition id {C} : tm fn_arity C _ := 
BaseTm Tid.
Definition map {C} : tm fn_arity C _ := 
BaseTm Tmap.
Definition nil {C} : tm fn_arity C _ := 
BaseTm Tnil.
Definition s {C} : tm fn_arity C _ := 
BaseTm Ts.
Definition zero {C} : tm fn_arity C _ := 
BaseTm Tzero.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, ∙) _
    (id ·  V 0)
     V 0.
Program Definition rule_1 := 
    make_rewrite
    (∙) _
    (add · zero)
    id.
Program Definition rule_2 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (add · (s ·  V 0) ·  V 1)
    (s · (add ·  V 0 ·  V 1)).
Program Definition rule_3 := 
    make_rewrite
    (_ ,, ∙) _
    (map ·  V 0 · nil)
    nil.
Program Definition rule_4 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (map ·  V 0 · (cons ·  V 1 ·  V 2))
    (cons · ( V 0 ·  V 1) · (map ·  V 0 ·  V 2)).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: rule_4 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tadd  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y0 * y1 + P_const 3 * y1))
| Tcons  => 
 λP
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 2 * y1))
| Tid  => 
 λP let y0 := P_var Vz in
(to_Poly (P_const 1 + P_const 3 * y0))
| Tmap  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 * y1 + P_const 3 * y1 * (G0 ·P (y1))))
| Tnil  => 
 (to_Poly (P_const 3))
| Ts  => 
 λP
(to_Poly (P_const 3))
| Tzero => 
(to_Poly (P_const 3))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
