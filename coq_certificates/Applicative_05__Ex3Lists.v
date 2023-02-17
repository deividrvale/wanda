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
| Tappend  
| Tcons  
| Tmap  
| Tnil.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tappend  =>  b ⟶ b ⟶ b
  | Tcons  =>  a ⟶ b ⟶ b
  | Tmap  =>  (a ⟶ a) ⟶ b ⟶ b
  | Tnil => b
end.
Definition append {C} : tm fn_arity C _ := 
BaseTm Tappend.
Definition cons {C} : tm fn_arity C _ := 
BaseTm Tcons.
Definition map {C} : tm fn_arity C _ := 
BaseTm Tmap.
Definition nil {C} : tm fn_arity C _ := 
BaseTm Tnil.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, ∙) _
    (append · nil ·  V 0)
     V 0.
Program Definition rule_1 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (append · (cons ·  V 0 ·  V 1) ·  V 2)
    (cons ·  V 0 · (append ·  V 1 ·  V 2)).
Program Definition rule_2 := 
    make_rewrite
    (_ ,, ∙) _
    (map ·  V 0 · nil)
    nil.
Program Definition rule_3 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (map ·  V 0 · (cons ·  V 1 ·  V 2))
    (cons · ( V 0 ·  V 1) · (map ·  V 0 ·  V 2)).
Program Definition rule_4 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (append · (append ·  V 0 ·  V 1) ·  V 2)
    (append ·  V 0 · (append ·  V 1 ·  V 2)).
Program Definition rule_5 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (map ·  V 0 · (append ·  V 1 ·  V 2))
    (append · (map ·  V 0 ·  V 1) · (map ·  V 0 ·  V 2)).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: rule_4 :: rule_5 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tappend  => 
 λP let y0 := P_var (Vs Vz) in
λP
(to_Poly (P_const 3 + P_const 2 * y0))
| Tcons  => 
 λP
λP
(to_Poly (P_const 3))
| Tmap  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 * y1 + P_const 3 * y1 * (G0 ·P (y1))))
| Tnil => 
(to_Poly (P_const 3))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
