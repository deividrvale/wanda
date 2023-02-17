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
| Tcons  
| Tcopy  
| Tf  
| Tfalse  
| Tfilter  
| Tfilter2  
| Tmap  
| Tn  
| Tnil  
| Ts  
| Ttrue  
| Tzero.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tcons  =>  c ⟶ c ⟶ c
  | Tcopy  =>  a ⟶ c ⟶ c ⟶ c
  | Tf  =>  c ⟶ c
  | Tfalse  =>  b
  | Tfilter  =>  (c ⟶ b) ⟶ c ⟶ c
  | Tfilter2  =>  b ⟶ (c ⟶ b) ⟶ c ⟶ c ⟶ c
  | Tmap  =>  (c ⟶ c) ⟶ c ⟶ c
  | Tn  =>  a
  | Tnil  =>  c
  | Ts  =>  a ⟶ a
  | Ttrue  =>  b
  | Tzero => a
end.
Definition cons {C} : tm fn_arity C _ := 
BaseTm Tcons.
Definition copy {C} : tm fn_arity C _ := 
BaseTm Tcopy.
Definition f {C} : tm fn_arity C _ := 
BaseTm Tf.
Definition false {C} : tm fn_arity C _ := 
BaseTm Tfalse.
Definition filter {C} : tm fn_arity C _ := 
BaseTm Tfilter.
Definition filter2 {C} : tm fn_arity C _ := 
BaseTm Tfilter2.
Definition map {C} : tm fn_arity C _ := 
BaseTm Tmap.
Definition n {C} : tm fn_arity C _ := 
BaseTm Tn.
Definition nil {C} : tm fn_arity C _ := 
BaseTm Tnil.
Definition s {C} : tm fn_arity C _ := 
BaseTm Ts.
Definition true {C} : tm fn_arity C _ := 
BaseTm Ttrue.
Definition zero {C} : tm fn_arity C _ := 
BaseTm Tzero.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, ∙) _
    (f · (cons · nil ·  V 0))
     V 0.
Program Definition rule_1 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (f · (cons · (f · (cons · nil ·  V 0)) ·  V 1))
    (copy · n ·  V 0 ·  V 1).
Program Definition rule_2 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (copy · zero ·  V 0 ·  V 1)
    (f ·  V 1).
Program Definition rule_3 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (copy · (s ·  V 0) ·  V 1 ·  V 2)
    (copy ·  V 0 ·  V 1 · (cons · (f ·  V 1) ·  V 2)).
Program Definition rule_4 := 
    make_rewrite
    (_ ,, ∙) _
    (map ·  V 0 · nil)
    nil.
Program Definition rule_5 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (map ·  V 0 · (cons ·  V 1 ·  V 2))
    (cons · ( V 0 ·  V 1) · (map ·  V 0 ·  V 2)).
Program Definition rule_6 := 
    make_rewrite
    (_ ,, ∙) _
    (filter ·  V 0 · nil)
    nil.
Program Definition rule_7 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (filter ·  V 0 · (cons ·  V 1 ·  V 2))
    (filter2 · ( V 0 ·  V 1) ·  V 0 ·  V 1 ·  V 2).
Program Definition rule_8 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (filter2 · true ·  V 0 ·  V 1 ·  V 2)
    (cons ·  V 1 · (filter ·  V 0 ·  V 2)).
Program Definition rule_9 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (filter2 · false ·  V 0 ·  V 1 ·  V 2)
    (filter ·  V 0 ·  V 2).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: rule_4 :: rule_5 :: rule_6 :: rule_7 :: rule_8 :: rule_9 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tcons  => 
 λP let y0 := P_var (Vs Vz) in
λP
(to_Poly (P_const 2 + P_const 3 * y0))
| Tcopy  => 
 λP let y0 := P_var (Vs (Vs Vz)) in
λP let y1 := P_var (Vs Vz) in
λP
(to_Poly (P_const 3 * y0 + P_const 3 * y0 * y1))
| Tf  => 
 λP
(to_Poly (P_const 2))
| Tfalse  => 
 (to_Poly (P_const 3))
| Tfilter  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 2 + P_const 2 * y1 + P_const 2 * (G0 ·P (y1)) + P_const 3 * y1 * (G0 ·P (y1))))
| Tfilter2  => 
 λP
λP let G1 := P_var (Vs (Vs Vz)) in
λP let y2 := P_var (Vs Vz) in
λP let y3 := P_var Vz in
(to_Poly (P_const 3 + P_const 2 * y3 + P_const 3 * y2 + P_const 2 * (G1 ·P (P_const 0)) + P_const 3 * y3 * (G1 ·P (y3)) + P_const 3 * (G1 ·P (y3))))
| Tmap  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 * y1 + P_const 3 * y1 * (G0 ·P (y1))))
| Tn  => 
 (to_Poly (P_const 0))
| Tnil  => 
 (to_Poly (P_const 3))
| Ts  => 
 λP let y0 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0))
| Ttrue  => 
 (to_Poly (P_const 3))
| Tzero => 
(to_Poly (P_const 3))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
