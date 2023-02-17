Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| Clist  
| Cnat.
Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.


Definition list := 
Base Clist.
Definition nat := 
Base Cnat.



Inductive fun_symbols := 
| Tcons  
| Tmap  
| Tmerge  
| Tnil.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tcons  =>  nat ⟶ list ⟶ list
  | Tmap  =>  (nat ⟶ nat) ⟶ list ⟶ list
  | Tmerge  =>  list ⟶ list ⟶ list ⟶ list
  | Tnil => list
end.
Definition cons {C} : tm fn_arity C _ := 
BaseTm Tcons.
Definition map {C} : tm fn_arity C _ := 
BaseTm Tmap.
Definition merge {C} : tm fn_arity C _ := 
BaseTm Tmerge.
Definition nil {C} : tm fn_arity C _ := 
BaseTm Tnil.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, ∙) _
    (merge · nil · nil ·  V 0)
     V 0.
Program Definition rule_1 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (merge · nil · (cons ·  V 0 ·  V 1) ·  V 2)
    (merge ·  V 1 · nil · (cons ·  V 0 ·  V 2)).
Program Definition rule_2 := 
    make_rewrite
    (_ ,, _ ,, _ ,, _ ,, ∙) _
    (merge · (cons ·  V 0 ·  V 1) ·  V 2 ·  V 3)
    (merge ·  V 2 ·  V 1 · (cons ·  V 0 ·  V 3)).
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
| Tcons  => 
 λP let y0 := P_var (Vs Vz) in
λP
(to_Poly (P_const 2 + y0))
| Tmap  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y1 + (G0 ·P (y1)) + P_const 2 * y1 * (G0 ·P (y1))))
| Tmerge  => 
 λP let y0 := P_var (Vs (Vs Vz)) in
λP let y1 := P_var (Vs Vz) in
λP
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y0 * y1 + P_const 3 * y1))
| Tnil => 
(to_Poly (P_const 2))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
