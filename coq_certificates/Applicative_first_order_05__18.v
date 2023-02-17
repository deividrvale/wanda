Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| Ca  
| Cb  
| Cc  
| Cd  
| Ce.
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
Definition e := 
Base Ce.



Inductive fun_symbols := 
| Tfacplus  
| Tfactimes  
| Tcons  
| Tfalse  
| Tfilter  
| Tfilter2  
| Tmap  
| Tnil  
| Ttrue.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tfacplus  =>  b ⟶ b ⟶ b
  | Tfactimes  =>  a ⟶ b ⟶ b
  | Tcons  =>  d ⟶ e ⟶ e
  | Tfalse  =>  c
  | Tfilter  =>  (d ⟶ c) ⟶ e ⟶ e
  | Tfilter2  =>  c ⟶ (d ⟶ c) ⟶ d ⟶ e ⟶ e
  | Tmap  =>  (d ⟶ d) ⟶ e ⟶ e
  | Tnil  =>  e
  | Ttrue => c
end.
Definition facplus {C} : tm fn_arity C _ := 
BaseTm Tfacplus.
Definition factimes {C} : tm fn_arity C _ := 
BaseTm Tfactimes.
Definition cons {C} : tm fn_arity C _ := 
BaseTm Tcons.
Definition false {C} : tm fn_arity C _ := 
BaseTm Tfalse.
Definition filter {C} : tm fn_arity C _ := 
BaseTm Tfilter.
Definition filter2 {C} : tm fn_arity C _ := 
BaseTm Tfilter2.
Definition map {C} : tm fn_arity C _ := 
BaseTm Tmap.
Definition nil {C} : tm fn_arity C _ := 
BaseTm Tnil.
Definition true {C} : tm fn_arity C _ := 
BaseTm Ttrue.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (factimes ·  V 0 · (facplus ·  V 1 ·  V 2))
    (facplus · (factimes ·  V 0 ·  V 1) · (factimes ·  V 0 ·  V 2)).
Program Definition rule_1 := 
    make_rewrite
    (_ ,, ∙) _
    (map ·  V 0 · nil)
    nil.
Program Definition rule_2 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (map ·  V 0 · (cons ·  V 1 ·  V 2))
    (cons · ( V 0 ·  V 1) · (map ·  V 0 ·  V 2)).
Program Definition rule_3 := 
    make_rewrite
    (_ ,, ∙) _
    (filter ·  V 0 · nil)
    nil.
Program Definition rule_4 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (filter ·  V 0 · (cons ·  V 1 ·  V 2))
    (filter2 · ( V 0 ·  V 1) ·  V 0 ·  V 1 ·  V 2).
Program Definition rule_5 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (filter2 · true ·  V 0 ·  V 1 ·  V 2)
    (cons ·  V 1 · (filter ·  V 0 ·  V 2)).
Program Definition rule_6 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (filter2 · false ·  V 0 ·  V 1 ·  V 2)
    (filter ·  V 0 ·  V 2).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: rule_4 :: rule_5 :: rule_6 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tfacplus  => 
 λP
λP
(to_Poly (P_const 3))
| Tfactimes  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (y1 + y0 * y1))
| Tcons  => 
 λP let y0 := P_var (Vs Vz) in
λP
(to_Poly (P_const 3 + P_const 3 * y0))
| Tfalse  => 
 (to_Poly (P_const 3))
| Tfilter  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y1 + (G0 ·P (P_const 0)) + (G0 ·P (y1)) + P_const 3 * y1 * (G0 ·P (y1))))
| Tfilter2  => 
 λP let y0 := P_var (Vs (Vs (Vs Vz))) in
λP let G1 := P_var (Vs (Vs Vz)) in
λP let y2 := P_var (Vs Vz) in
λP let y3 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y2 + P_const 3 * y3 + (G1 ·P (y2)) + P_const 2 * (G1 ·P (y3)) + P_const 3 * y3 * (G1 ·P (y3))))
| Tmap  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 * y1 + P_const 3 * y1 * (G0 ·P (y1))))
| Tnil  => 
 (to_Poly (P_const 3))
| Ttrue => 
(to_Poly (P_const 3))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
