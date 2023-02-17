Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| Ca.
Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.


Definition a := 
Base Ca.



Inductive fun_symbols := 
| Tappend  
| Tconcat  
| Tcons  
| Tflatten  
| Tmap  
| Tnil  
| Tnode.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tappend  =>  a ⟶ a ⟶ a
  | Tconcat  =>  a ⟶ a
  | Tcons  =>  a ⟶ a ⟶ a
  | Tflatten  =>  a ⟶ a
  | Tmap  =>  (a ⟶ a) ⟶ a ⟶ a
  | Tnil  =>  a
  | Tnode => a ⟶ a ⟶ a
end.
Definition append {C} : tm fn_arity C _ := 
BaseTm Tappend.
Definition concat {C} : tm fn_arity C _ := 
BaseTm Tconcat.
Definition cons {C} : tm fn_arity C _ := 
BaseTm Tcons.
Definition flatten {C} : tm fn_arity C _ := 
BaseTm Tflatten.
Definition map {C} : tm fn_arity C _ := 
BaseTm Tmap.
Definition nil {C} : tm fn_arity C _ := 
BaseTm Tnil.
Definition node {C} : tm fn_arity C _ := 
BaseTm Tnode.



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
    (_ ,, _ ,, ∙) _
    (flatten · (node ·  V 0 ·  V 1))
    (cons ·  V 0 · (concat · (map · flatten ·  V 1))).
Program Definition rule_3 := 
    make_rewrite
    (∙) _
    (concat · nil)
    nil.
Program Definition rule_4 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (concat · (cons ·  V 0 ·  V 1))
    (append ·  V 0 · (concat ·  V 1)).
Program Definition rule_5 := 
    make_rewrite
    (_ ,, ∙) _
    (append · nil ·  V 0)
     V 0.
Program Definition rule_6 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (append · (cons ·  V 0 ·  V 1) ·  V 2)
    (cons ·  V 0 · (append ·  V 1 ·  V 2)).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: rule_4 :: rule_5 :: rule_6 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tappend  => 
 λP let y0 := P_var (Vs Vz) in
λP
(to_Poly (y0))
| Tconcat  => 
 λP let y0 := P_var Vz in
(to_Poly (y0))
| Tcons  => 
 λP
λP
(to_Poly (P_const 2))
| Tflatten  => 
 λP
(to_Poly (P_const 0))
| Tmap  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (y1 + P_const 3 * y1 * (G0 ·P (y1)) + P_const 3 * (G0 ·P (y1))))
| Tnil  => 
 (to_Poly (P_const 3))
| Tnode => 
λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y0 * y1 + P_const 3 * y1))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
