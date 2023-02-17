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
| Teq  
| Tfalse  
| Tfork  
| TIF  
| Tlt  
| Tmember  
| Tnull  
| Ts  
| Ttrue  
| Tzero.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Teq  =>  a ⟶ a ⟶ c
  | Tfalse  =>  c
  | Tfork  =>  b ⟶ a ⟶ b ⟶ b
  | TIF  =>  c ⟶ c ⟶ c ⟶ c
  | Tlt  =>  a ⟶ a ⟶ c
  | Tmember  =>  a ⟶ b ⟶ c
  | Tnull  =>  b
  | Ts  =>  a ⟶ a
  | Ttrue  =>  c
  | Tzero => a
end.
Definition eq {C} : tm fn_arity C _ := 
BaseTm Teq.
Definition false {C} : tm fn_arity C _ := 
BaseTm Tfalse.
Definition fork {C} : tm fn_arity C _ := 
BaseTm Tfork.
Definition IF {C} : tm fn_arity C _ := 
BaseTm TIF.
Definition lt {C} : tm fn_arity C _ := 
BaseTm Tlt.
Definition member {C} : tm fn_arity C _ := 
BaseTm Tmember.
Definition null {C} : tm fn_arity C _ := 
BaseTm Tnull.
Definition s {C} : tm fn_arity C _ := 
BaseTm Ts.
Definition true {C} : tm fn_arity C _ := 
BaseTm Ttrue.
Definition zero {C} : tm fn_arity C _ := 
BaseTm Tzero.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (lt · (s ·  V 0) · (s ·  V 1))
    (lt ·  V 0 ·  V 1).
Program Definition rule_1 := 
    make_rewrite
    (_ ,, ∙) _
    (lt · zero · (s ·  V 0))
    true.
Program Definition rule_2 := 
    make_rewrite
    (_ ,, ∙) _
    (lt ·  V 0 · zero)
    false.
Program Definition rule_3 := 
    make_rewrite
    (_ ,, ∙) _
    (eq ·  V 0 ·  V 0)
    true.
Program Definition rule_4 := 
    make_rewrite
    (_ ,, ∙) _
    (eq · (s ·  V 0) · zero)
    false.
Program Definition rule_5 := 
    make_rewrite
    (_ ,, ∙) _
    (eq · zero · (s ·  V 0))
    false.
Program Definition rule_6 := 
    make_rewrite
    (_ ,, ∙) _
    (member ·  V 0 · null)
    false.
Program Definition rule_7 := 
    make_rewrite
    (_ ,, _ ,, _ ,, _ ,, ∙) _
    (member ·  V 0 · (fork ·  V 1 ·  V 2 ·  V 3))
    (IF · (lt ·  V 0 ·  V 2) · (member ·  V 0 ·  V 1) · (IF · (eq ·  V 0 ·  V 2) · true · (member ·  V 0 ·  V 3))).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: rule_4 :: rule_5 :: rule_6 :: rule_7 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Teq  => 
 λP
λP
(to_Poly (P_const 1))
| Tfalse  => 
 (to_Poly (P_const 0))
| Tfork  => 
 λP let y0 := P_var (Vs (Vs Vz)) in
λP let y1 := P_var (Vs Vz) in
λP let y2 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y0 * y1 + P_const 3 * y0 * y2 + P_const 3 * y1 + P_const 3 * y1 * y2 + P_const 3 * y2))
| TIF  => 
 λP
λP
λP
(to_Poly (P_const 0))
| Tlt  => 
 λP let y0 := P_var (Vs Vz) in
λP
(to_Poly (y0))
| Tmember  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 2 * y0 * y1 + P_const 2 * y1))
| Tnull  => 
 (to_Poly (P_const 3))
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
