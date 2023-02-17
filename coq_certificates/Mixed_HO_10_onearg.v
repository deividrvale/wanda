Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| Cbool  
| Cnat.
Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.


Definition bool := 
Base Cbool.
Definition nat := 
Base Cnat.



Inductive fun_symbols := 
| Tadd  
| Teq  
| Terr  
| Tfalse  
| Tid  
| Tnul  
| Tpred  
| Ts  
| Ttrue  
| Tzero.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tadd  =>  nat ⟶ nat ⟶ nat
  | Teq  =>  nat ⟶ nat ⟶ bool
  | Terr  =>  nat
  | Tfalse  =>  bool
  | Tid  =>  nat ⟶ nat
  | Tnul  =>  nat ⟶ bool
  | Tpred  =>  nat ⟶ nat
  | Ts  =>  nat ⟶ nat
  | Ttrue  =>  bool
  | Tzero => nat
end.
Definition add {C} : tm fn_arity C _ := 
BaseTm Tadd.
Definition eq {C} : tm fn_arity C _ := 
BaseTm Teq.
Definition err {C} : tm fn_arity C _ := 
BaseTm Terr.
Definition false {C} : tm fn_arity C _ := 
BaseTm Tfalse.
Definition id {C} : tm fn_arity C _ := 
BaseTm Tid.
Definition nul {C} : tm fn_arity C _ := 
BaseTm Tnul.
Definition pred {C} : tm fn_arity C _ := 
BaseTm Tpred.
Definition s {C} : tm fn_arity C _ := 
BaseTm Ts.
Definition true {C} : tm fn_arity C _ := 
BaseTm Ttrue.
Definition zero {C} : tm fn_arity C _ := 
BaseTm Tzero.



Program Definition rule_0 := 
    make_rewrite
    (∙) _
    (nul · zero)
    true.
Program Definition rule_1 := 
    make_rewrite
    (_ ,, ∙) _
    (nul · (s ·  V 0))
    false.
Program Definition rule_2 := 
    make_rewrite
    (∙) _
    (nul · err)
    false.
Program Definition rule_3 := 
    make_rewrite
    (∙) _
    (pred · zero)
    err.
Program Definition rule_4 := 
    make_rewrite
    (_ ,, ∙) _
    (pred · (s ·  V 0))
     V 0.
Program Definition rule_5 := 
    make_rewrite
    (_ ,, ∙) _
    (id ·  V 0)
     V 0.
Program Definition rule_6 := 
    make_rewrite
    (∙) _
    (eq · zero)
    nul.
Program Definition rule_7 := 
    make_rewrite
    (_ ,, ∙) _
    (eq · (s ·  V 0))
    (λ eq ·  V 1 · (pred ·  V 0)).
Program Definition rule_8 := 
    make_rewrite
    (∙) _
    (add · zero)
    id.
Program Definition rule_9 := 
    make_rewrite
    (_ ,, ∙) _
    (add · (s ·  V 0))
    (λ add ·  V 1 · (s ·  V 0)).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: rule_4 :: rule_5 :: rule_6 :: rule_7 :: rule_8 :: rule_9 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tadd  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y0 * y1))
| Teq  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y0 * y1))
| Terr  => 
 (to_Poly (P_const 0))
| Tfalse  => 
 (to_Poly (P_const 0))
| Tid  => 
 λP
(to_Poly (P_const 1))
| Tnul  => 
 λP
(to_Poly (P_const 2))
| Tpred  => 
 λP
(to_Poly (P_const 0))
| Ts  => 
 λP let y0 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0))
| Ttrue  => 
 (to_Poly (P_const 0))
| Tzero => 
(to_Poly (P_const 3))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
