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
| Tbranch  
| Tleaf  
| Tmapbt.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tbranch  =>  a ⟶ b ⟶ b ⟶ b
  | Tleaf  =>  a ⟶ b
  | Tmapbt => (a ⟶ a) ⟶ b ⟶ b
end.
Definition branch {C} : tm fn_arity C _ := 
BaseTm Tbranch.
Definition leaf {C} : tm fn_arity C _ := 
BaseTm Tleaf.
Definition mapbt {C} : tm fn_arity C _ := 
BaseTm Tmapbt.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (mapbt ·  V 0 · (leaf ·  V 1))
    (leaf · ( V 0 ·  V 1)).
Program Definition rule_1 := 
    make_rewrite
    (_ ,, _ ,, _ ,, _ ,, ∙) _
    (mapbt ·  V 0 · (branch ·  V 1 ·  V 2 ·  V 3))
    (branch · ( V 0 ·  V 1) · (mapbt ·  V 0 ·  V 2) · (mapbt ·  V 0 ·  V 3)).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tbranch  => 
 λP
λP
λP
(to_Poly (P_const 3))
| Tleaf  => 
 λP
(to_Poly (P_const 3))
| Tmapbt => 
λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 * y1 + (G0 ·P (y1)) + P_const 3 * y1 * (G0 ·P (y1))))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
