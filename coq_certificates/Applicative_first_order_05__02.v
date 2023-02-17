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
| Tfacdot  
| Tcons  
| Tfalse  
| Tfilter  
| Tfilter2  
| Ti  
| Tmap  
| Tnil  
| Tone  
| Ttrue.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tfacdot  =>  a ⟶ a ⟶ a
  | Tcons  =>  c ⟶ d ⟶ d
  | Tfalse  =>  b
  | Tfilter  =>  (c ⟶ b) ⟶ d ⟶ d
  | Tfilter2  =>  b ⟶ (c ⟶ b) ⟶ c ⟶ d ⟶ d
  | Ti  =>  a ⟶ a
  | Tmap  =>  (c ⟶ c) ⟶ d ⟶ d
  | Tnil  =>  d
  | Tone  =>  a
  | Ttrue => b
end.
Definition facdot {C} : tm fn_arity C _ := 
BaseTm Tfacdot.
Definition cons {C} : tm fn_arity C _ := 
BaseTm Tcons.
Definition false {C} : tm fn_arity C _ := 
BaseTm Tfalse.
Definition filter {C} : tm fn_arity C _ := 
BaseTm Tfilter.
Definition filter2 {C} : tm fn_arity C _ := 
BaseTm Tfilter2.
Definition i {C} : tm fn_arity C _ := 
BaseTm Ti.
Definition map {C} : tm fn_arity C _ := 
BaseTm Tmap.
Definition nil {C} : tm fn_arity C _ := 
BaseTm Tnil.
Definition one {C} : tm fn_arity C _ := 
BaseTm Tone.
Definition true {C} : tm fn_arity C _ := 
BaseTm Ttrue.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, ∙) _
    (facdot · one ·  V 0)
     V 0.
Program Definition rule_1 := 
    make_rewrite
    (_ ,, ∙) _
    (facdot ·  V 0 · one)
     V 0.
Program Definition rule_2 := 
    make_rewrite
    (_ ,, ∙) _
    (facdot · (i ·  V 0) ·  V 0)
    one.
Program Definition rule_3 := 
    make_rewrite
    (_ ,, ∙) _
    (facdot ·  V 0 · (i ·  V 0))
    one.
Program Definition rule_4 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (facdot · (i ·  V 0) · (facdot ·  V 0 ·  V 1))
     V 1.
Program Definition rule_5 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (facdot ·  V 0 · (facdot · (i ·  V 0) ·  V 1))
     V 1.
Program Definition rule_6 := 
    make_rewrite
    (∙) _
    (i · one)
    one.
Program Definition rule_7 := 
    make_rewrite
    (_ ,, ∙) _
    (i · (i ·  V 0))
     V 0.
Program Definition rule_8 := 
    make_rewrite
    (_ ,, ∙) _
    (map ·  V 0 · nil)
    nil.
Program Definition rule_9 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (map ·  V 0 · (cons ·  V 1 ·  V 2))
    (cons · ( V 0 ·  V 1) · (map ·  V 0 ·  V 2)).
Program Definition rule_10 := 
    make_rewrite
    (_ ,, ∙) _
    (filter ·  V 0 · nil)
    nil.
Program Definition rule_11 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (filter ·  V 0 · (cons ·  V 1 ·  V 2))
    (filter2 · ( V 0 ·  V 1) ·  V 0 ·  V 1 ·  V 2).
Program Definition rule_12 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (filter2 · true ·  V 0 ·  V 1 ·  V 2)
    (cons ·  V 1 · (filter ·  V 0 ·  V 2)).
Program Definition rule_13 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (filter2 · false ·  V 0 ·  V 1 ·  V 2)
    (filter ·  V 0 ·  V 2).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: rule_4 :: rule_5 :: rule_6 :: rule_7 :: rule_8 :: rule_9 :: rule_10 :: rule_11 :: rule_12 :: rule_13 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tfacdot  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y0 * y1 + P_const 3 * y1))
| Tcons  => 
 λP let y0 := P_var (Vs Vz) in
λP
(to_Poly (P_const 3 + y0))
| Tfalse  => 
 (to_Poly (P_const 3))
| Tfilter  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 1 + P_const 2 * y1 + P_const 3 * y1 * (G0 ·P (y1)) + P_const 3 * (G0 ·P (P_const 0))))
| Tfilter2  => 
 λP
λP let G1 := P_var (Vs (Vs Vz)) in
λP let y2 := P_var (Vs Vz) in
λP let y3 := P_var Vz in
(to_Poly (P_const 2 + y2 + P_const 2 * y3 + (G1 ·P (y2)) + P_const 3 * y3 * (G1 ·P (y3)) + P_const 3 * (G1 ·P (P_const 0)) + P_const 3 * (G1 ·P (y3))))
| Ti  => 
 λP let y0 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0))
| Tmap  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 * y1 + P_const 2 * (G0 ·P (y1)) + y1 * (G0 ·P (y1))))
| Tnil  => 
 (to_Poly (P_const 3))
| Tone  => 
 (to_Poly (P_const 0))
| Ttrue => 
(to_Poly (P_const 3))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
