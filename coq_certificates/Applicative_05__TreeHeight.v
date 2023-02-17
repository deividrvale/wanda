Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| Ca  
| Cb  
| Cc  
| Cd.
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
Definition d := 
Base Cd.



Inductive fun_symbols := 
| Tcons  
| Tfalse  
| Theight  
| TIF  
| Tle  
| Tmap  
| Tmaxlist  
| Tnil  
| Tnode  
| Ts  
| Ttrue  
| Tzero.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tcons  =>  d ⟶ c ⟶ c
  | Tfalse  =>  a
  | Theight  =>  d ⟶ d
  | TIF  =>  a ⟶ d ⟶ d
  | Tle  =>  d ⟶ d ⟶ a
  | Tmap  =>  (d ⟶ d) ⟶ c ⟶ c
  | Tmaxlist  =>  d ⟶ c ⟶ d
  | Tnil  =>  c
  | Tnode  =>  b ⟶ c ⟶ d
  | Ts  =>  d ⟶ d
  | Ttrue  =>  a
  | Tzero => d
end.
Definition cons {C} : tm fn_arity C _ := 
BaseTm Tcons.
Definition false {C} : tm fn_arity C _ := 
BaseTm Tfalse.
Definition height {C} : tm fn_arity C _ := 
BaseTm Theight.
Definition IF {C} : tm fn_arity C _ := 
BaseTm TIF.
Definition le {C} : tm fn_arity C _ := 
BaseTm Tle.
Definition map {C} : tm fn_arity C _ := 
BaseTm Tmap.
Definition maxlist {C} : tm fn_arity C _ := 
BaseTm Tmaxlist.
Definition nil {C} : tm fn_arity C _ := 
BaseTm Tnil.
Definition node {C} : tm fn_arity C _ := 
BaseTm Tnode.
Definition s {C} : tm fn_arity C _ := 
BaseTm Ts.
Definition true {C} : tm fn_arity C _ := 
BaseTm Ttrue.
Definition zero {C} : tm fn_arity C _ := 
BaseTm Tzero.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, ∙) _
    (map ·  V 0 · nil)
    nil.
Program Definition rule_1 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (map ·  V 0 · (cons ·  V 1 ·  V 2))
    (cons · ( V 0 ·  V 1) · (map ·  V 0 ·  V 2)).
Program Definition rule_2 := 
    make_rewrite
    (_ ,, ∙) _
    (le · zero ·  V 0)
    true.
Program Definition rule_3 := 
    make_rewrite
    (_ ,, ∙) _
    (le · (s ·  V 0) · zero)
    false.
Program Definition rule_4 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (le · (s ·  V 0) · (s ·  V 1))
    (le ·  V 0 ·  V 1).
Program Definition rule_5 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (maxlist ·  V 0 · (cons ·  V 1 ·  V 2))
    (IF · (le ·  V 0 ·  V 1) · (maxlist ·  V 1 ·  V 2)).
Program Definition rule_6 := 
    make_rewrite
    (_ ,, ∙) _
    (maxlist ·  V 0 · nil)
     V 0.
Program Definition rule_7 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (height · (node ·  V 0 ·  V 1))
    (s · (maxlist · zero · (map · height ·  V 1))).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: rule_4 :: rule_5 :: rule_6 :: rule_7 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tcons  => 
 λP
λP
(to_Poly (P_const 3))
| Tfalse  => 
 (to_Poly (P_const 0))
| Theight  => 
 λP
(to_Poly (P_const 0))
| TIF  => 
 λP
λP
(to_Poly (P_const 0))
| Tle  => 
 λP
λP
(to_Poly (P_const 3))
| Tmap  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (y1 + P_const 3 * y1 * (G0 ·P (y1)) + P_const 3 * (G0 ·P (y1))))
| Tmaxlist  => 
 λP
λP let y1 := P_var Vz in
(to_Poly (y1))
| Tnil  => 
 (to_Poly (P_const 3))
| Tnode  => 
 λP
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y1))
| Ts  => 
 λP
(to_Poly (P_const 1))
| Ttrue  => 
 (to_Poly (P_const 0))
| Tzero => 
(to_Poly (P_const 0))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
