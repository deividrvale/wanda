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
| Tappend  
| Tcons  
| Tflatwith  
| Tflatwithsub  
| Tleaf  
| Tnil  
| Tnode.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tappend  =>  c ⟶ c ⟶ c
  | Tcons  =>  b ⟶ c ⟶ c
  | Tflatwith  =>  (a ⟶ b) ⟶ b ⟶ c
  | Tflatwithsub  =>  (a ⟶ b) ⟶ c ⟶ c
  | Tleaf  =>  a ⟶ b
  | Tnil  =>  c
  | Tnode => c ⟶ b
end.
Definition append {C} : tm fn_arity C _ := 
BaseTm Tappend.
Definition cons {C} : tm fn_arity C _ := 
BaseTm Tcons.
Definition flatwith {C} : tm fn_arity C _ := 
BaseTm Tflatwith.
Definition flatwithsub {C} : tm fn_arity C _ := 
BaseTm Tflatwithsub.
Definition leaf {C} : tm fn_arity C _ := 
BaseTm Tleaf.
Definition nil {C} : tm fn_arity C _ := 
BaseTm Tnil.
Definition node {C} : tm fn_arity C _ := 
BaseTm Tnode.



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
    (_ ,, _ ,, ∙) _
    (flatwith ·  V 0 · (leaf ·  V 1))
    (cons · ( V 0 ·  V 1) · nil).
Program Definition rule_3 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (flatwith ·  V 0 · (node ·  V 1))
    (flatwithsub ·  V 0 ·  V 1).
Program Definition rule_4 := 
    make_rewrite
    (_ ,, ∙) _
    (flatwithsub ·  V 0 · nil)
    nil.
Program Definition rule_5 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (flatwithsub ·  V 0 · (cons ·  V 1 ·  V 2))
    (append · (flatwith ·  V 0 ·  V 1) · (flatwithsub ·  V 0 ·  V 2)).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: rule_4 :: rule_5 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tappend  => 
 λP let y0 := P_var (Vs Vz) in
λP
(to_Poly (y0))
| Tcons  => 
 λP let y0 := P_var (Vs Vz) in
λP
(to_Poly (P_const 2 + P_const 2 * y0))
| Tflatwith  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 2 * y1 + P_const 3 * y1 * (G0 ·P (y1))))
| Tflatwithsub  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y1 + (G0 ·P (y1)) + P_const 3 * y1 * (G0 ·P (y1))))
| Tleaf  => 
 λP let y0 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0))
| Tnil  => 
 (to_Poly (P_const 1))
| Tnode => 
λP let y0 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
