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
| Tleaf  
| Tmapt  
| Tmaptlist  
| Tnil  
| Tnode.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tcons  =>  b ⟶ c ⟶ c
  | Tleaf  =>  a ⟶ b
  | Tmapt  =>  (a ⟶ a) ⟶ b ⟶ b
  | Tmaptlist  =>  (a ⟶ a) ⟶ c ⟶ c
  | Tnil  =>  c
  | Tnode => c ⟶ b
end.
Definition cons {C} : tm fn_arity C _ := 
BaseTm Tcons.
Definition leaf {C} : tm fn_arity C _ := 
BaseTm Tleaf.
Definition mapt {C} : tm fn_arity C _ := 
BaseTm Tmapt.
Definition maptlist {C} : tm fn_arity C _ := 
BaseTm Tmaptlist.
Definition nil {C} : tm fn_arity C _ := 
BaseTm Tnil.
Definition node {C} : tm fn_arity C _ := 
BaseTm Tnode.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (mapt ·  V 0 · (leaf ·  V 1))
    (leaf · ( V 0 ·  V 1)).
Program Definition rule_1 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (mapt ·  V 0 · (node ·  V 1))
    (node · (maptlist ·  V 0 ·  V 1)).
Program Definition rule_2 := 
    make_rewrite
    (_ ,, ∙) _
    (maptlist ·  V 0 · nil)
    nil.
Program Definition rule_3 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (maptlist ·  V 0 · (cons ·  V 1 ·  V 2))
    (cons · (mapt ·  V 0 ·  V 1) · (maptlist ·  V 0 ·  V 2)).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tcons  => 
 λP
λP
(to_Poly (P_const 3))
| Tleaf  => 
 λP
(to_Poly (P_const 3))
| Tmapt  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 * y1 + P_const 3 * y1 * (G0 ·P (y1))))
| Tmaptlist  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 * y1 + P_const 2 * (G0 ·P (y1)) + P_const 3 * y1 * (G0 ·P (y1))))
| Tnil  => 
 (to_Poly (P_const 3))
| Tnode => 
λP let y0 := P_var Vz in
(to_Poly (P_const 3 + y0))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
