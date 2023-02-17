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
| Tid  
| Tplus  
| Ts  
| Tzero.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tid  =>  a ⟶ a
  | Tplus  =>  a ⟶ a ⟶ a
  | Ts  =>  a ⟶ a
  | Tzero => a
end.
Definition id {C} : tm fn_arity C _ := 
BaseTm Tid.
Definition plus {C} : tm fn_arity C _ := 
BaseTm Tplus.
Definition s {C} : tm fn_arity C _ := 
BaseTm Ts.
Definition zero {C} : tm fn_arity C _ := 
BaseTm Tzero.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, ∙) _
    (id ·  V 0)
     V 0.
Program Definition rule_1 := 
    make_rewrite
    (∙) _
    (plus · zero)
    id.
Program Definition rule_2 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (plus · (s ·  V 0) ·  V 1)
    (s · (plus ·  V 0 ·  V 1)).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tid  => 
 λP let y0 := P_var Vz in
(to_Poly (P_const 1 + P_const 3 * y0))
| Tplus  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y0 * y1 + P_const 3 * y1))
| Ts  => 
 λP
(to_Poly (P_const 3))
| Tzero => 
(to_Poly (P_const 3))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
