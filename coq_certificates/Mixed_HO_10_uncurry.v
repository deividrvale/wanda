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
| Tf  
| Tf1  
| Tf2.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tf  =>  a ⟶ b ⟶ c
  | Tf1  =>  a ⟶ b ⟶ c
  | Tf2 => a ⟶ b ⟶ c
end.
Definition f {C} : tm fn_arity C _ := 
BaseTm Tf.
Definition f1 {C} : tm fn_arity C _ := 
BaseTm Tf1.
Definition f2 {C} : tm fn_arity C _ := 
BaseTm Tf2.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, ∙) _
    (f ·  V 0)
    (f1 ·  V 0).
Program Definition rule_1 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (f1 ·  V 0 ·  V 1)
    (f2 ·  V 0 ·  V 1).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tf  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y0 * y1 + P_const 3 * y1))
| Tf1  => 
 λP
λP
(to_Poly (P_const 1))
| Tf2 => 
λP
λP
(to_Poly (P_const 0))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
