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
| Tmap  
| Tnil  
| Tnode  
| Tplus  
| Ts  
| Tsize  
| Tsum  
| Tzero.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tcons  =>  c ⟶ b ⟶ b
  | Tmap  =>  (c ⟶ c) ⟶ b ⟶ b
  | Tnil  =>  b
  | Tnode  =>  a ⟶ b ⟶ c
  | Tplus  =>  c ⟶ c ⟶ c
  | Ts  =>  c ⟶ c
  | Tsize  =>  c ⟶ c
  | Tsum  =>  b ⟶ c
  | Tzero => c
end.
Definition cons {C} : tm fn_arity C _ := 
BaseTm Tcons.
Definition map {C} : tm fn_arity C _ := 
BaseTm Tmap.
Definition nil {C} : tm fn_arity C _ := 
BaseTm Tnil.
Definition node {C} : tm fn_arity C _ := 
BaseTm Tnode.
Definition plus {C} : tm fn_arity C _ := 
BaseTm Tplus.
Definition s {C} : tm fn_arity C _ := 
BaseTm Ts.
Definition size {C} : tm fn_arity C _ := 
BaseTm Tsize.
Definition sum {C} : tm fn_arity C _ := 
BaseTm Tsum.
Definition zero {C} : tm fn_arity C _ := 
BaseTm Tzero.



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
    (sum · (cons ·  V 0 ·  V 1))
    (plus ·  V 0 · (sum ·  V 1)).
Program Definition rule_3 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (size · (node ·  V 0 ·  V 1))
    (s · (sum · (map · size ·  V 1))).
Program Definition rule_4 := 
    make_rewrite
    (_ ,, ∙) _
    (plus · zero ·  V 0)
    zero.
Program Definition rule_5 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (plus · (s ·  V 0) ·  V 1)
    (s · (plus ·  V 0 ·  V 1)).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: rule_4 :: rule_5 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tcons  => 
 λP
λP
(to_Poly (P_const 3))
| Tmap  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (y1 + (G0 ·P (y1)) + P_const 3 * y1 * (G0 ·P (y1))))
| Tnil  => 
 (to_Poly (P_const 3))
| Tnode  => 
 λP
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y1))
| Tplus  => 
 λP let y0 := P_var (Vs Vz) in
λP
(to_Poly (y0))
| Ts  => 
 λP
(to_Poly (P_const 1))
| Tsize  => 
 λP
(to_Poly (P_const 0))
| Tsum  => 
 λP let y0 := P_var Vz in
(to_Poly (y0))
| Tzero => 
(to_Poly (P_const 3))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
