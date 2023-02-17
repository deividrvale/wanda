Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| CA  
| CB.
Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.


Definition A := 
Base CA.
Definition B := 
Base CB.



Inductive fun_symbols := 
| Ta  
| Tb  
| Tc  
| Tf.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Ta  =>  B
  | Tb  =>  B
  | Tc  =>  B
  | Tf => (A ⟶ B) ⟶ B
end.
Definition a {C} : tm fn_arity C _ := 
BaseTm Ta.
Definition b {C} : tm fn_arity C _ := 
BaseTm Tb.
Definition c {C} : tm fn_arity C _ := 
BaseTm Tc.
Definition f {C} : tm fn_arity C _ := 
BaseTm Tf.



Program Definition rule_0 := 
    make_rewrite
    (∙) _
    (f · (λ a))
    b.
Program Definition rule_1 := 
    make_rewrite
    (∙) _
    b
    (f · (λ c)).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Ta  => 
 (to_Poly (P_const 3))
| Tb  => 
 (to_Poly (P_const 2))
| Tc  => 
 (to_Poly (P_const 0))
| Tf => 
λP let G0 := P_var Vz in
(to_Poly (P_const 3 * (G0 ·P (P_const 0))))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
