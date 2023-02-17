Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| CN  
| Cf  
| Ct.
Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.


Definition N := 
Base CN.
Definition f := 
Base Cf.
Definition t := 
Base Ct.



Inductive fun_symbols := 
| Tcons  
| Theightf  
| Theightt  
| Tleaf  
| Tmax  
| Tnil  
| Tnode  
| Ts  
| Tz.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tcons  =>  t ⟶ f ⟶ f
  | Theightf  =>  f ⟶ N
  | Theightt  =>  t ⟶ N
  | Tleaf  =>  t
  | Tmax  =>  N ⟶ N ⟶ N
  | Tnil  =>  f
  | Tnode  =>  f ⟶ t
  | Ts  =>  N ⟶ N
  | Tz => N
end.
Definition cons {C} : tm fn_arity C _ := 
BaseTm Tcons.
Definition heightf {C} : tm fn_arity C _ := 
BaseTm Theightf.
Definition heightt {C} : tm fn_arity C _ := 
BaseTm Theightt.
Definition leaf {C} : tm fn_arity C _ := 
BaseTm Tleaf.
Definition max {C} : tm fn_arity C _ := 
BaseTm Tmax.
Definition nil {C} : tm fn_arity C _ := 
BaseTm Tnil.
Definition node {C} : tm fn_arity C _ := 
BaseTm Tnode.
Definition s {C} : tm fn_arity C _ := 
BaseTm Ts.
Definition z {C} : tm fn_arity C _ := 
BaseTm Tz.



Program Definition rule_0 := 
    make_rewrite
    (∙) _
    (heightf · nil)
    z.
Program Definition rule_1 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (heightf · (cons ·  V 0 ·  V 1))
    (max · (heightt ·  V 0) · (heightf ·  V 1)).
Program Definition rule_2 := 
    make_rewrite
    (∙) _
    (heightt · leaf)
    z.
Program Definition rule_3 := 
    make_rewrite
    (_ ,, ∙) _
    (heightt · (node ·  V 0))
    (s · (heightf ·  V 0)).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tcons  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y0 * y1 + P_const 3 * y1))
| Theightf  => 
 λP
(to_Poly (P_const 0))
| Theightt  => 
 λP
(to_Poly (P_const 0))
| Tleaf  => 
 (to_Poly (P_const 3))
| Tmax  => 
 λP
λP
(to_Poly (P_const 0))
| Tnil  => 
 (to_Poly (P_const 3))
| Tnode  => 
 λP let y0 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0))
| Ts  => 
 λP
(to_Poly (P_const 0))
| Tz => 
(to_Poly (P_const 0))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
