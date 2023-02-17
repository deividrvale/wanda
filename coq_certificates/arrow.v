Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| Cc  
| Ct.
Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.


Definition c := 
Base Cc.
Definition t := 
Base Ct.



Inductive fun_symbols := 
| Tand  
| Tarrow  
| Tlessthan.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tand  =>  c ⟶ c ⟶ c
  | Tarrow  =>  t ⟶ t ⟶ t
  | Tlessthan => t ⟶ t ⟶ c
end.
Definition and {C} : tm fn_arity C _ := 
BaseTm Tand.
Definition arrow {C} : tm fn_arity C _ := 
BaseTm Tarrow.
Definition lessthan {C} : tm fn_arity C _ := 
BaseTm Tlessthan.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, _ ,, _ ,, _ ,, ∙) _
    (lessthan · (arrow ·  V 0 ·  V 1) · (arrow ·  V 2 ·  V 3))
    (and · (lessthan ·  V 2 ·  V 0) · (lessthan ·  V 1 ·  V 3)).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tand  => 
 λP
λP
(to_Poly (P_const 0))
| Tarrow  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y0 * y1 + P_const 3 * y1))
| Tlessthan => 
λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 * y0 * y1))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
