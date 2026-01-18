theory LinkingPreserve_Aux
  imports Deterministic
begin 

lemma link_exec_aux: 
  "\<lbrakk> M, \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'; link_wf M M' \<rbrakk> \<Longrightarrow> (M \<circ>\<^bsub>l\<^esub> M'), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'"
  unfolding link_wf_def moduleLinking_def 
            moduleAux_def dom_def build_call_frame_def
proof (induction  rule: exec.induct)
  case (exec_method_call \<phi> x y m params stmts \<alpha> \<chi> C paramValues M meth \<phi>'' \<psi>)
  thus ?case 
    by (simp add: exec.exec_method_call ident_lookup.induct 
        \<M>_def split: option.splits)     
next
  case (exec_var_assign \<phi> x y stmts M \<psi> \<chi>)
  thus ?case
    apply (simp add: this_field_lookup.induct)
    using exec.exec_var_assign by auto 
next
  case (exec_field_assign \<phi> y x stmts v \<chi> \<chi>' M \<psi>)
  thus ?case
  apply (simp add: this_field_lookup.induct ident_lookup.induct)
    by (simp add: exec.exec_field_assign) 
next
  case (exec_new \<phi> x C params stmts paramValues M c obj' \<alpha> \<chi> \<chi>' \<psi>)
  thus ?case 
    by (simp add: ident_lookup.induct exec.exec_new)   
next
  case (exec_return \<phi> x stmts \<phi>' x' stmts' M \<psi> \<chi>)
  thus ?case
    apply (simp add: ident_lookup.induct)
    using exec.exec_return by auto   
qed

lemma internal_linking_1_aux:
  "\<lbrakk>M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>'; link_wf_3M M M' M''\<rbrakk> \<Longrightarrow> 
         M; (M' \<circ>\<^bsub>l\<^esub> M''), \<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>'"
proof (induction rule: internal_exec.induct)
  case (internal_exec_first_step  \<sigma> \<sigma>' c c')
  have a:  "link_wf M (M' \<circ>\<^bsub>l\<^esub> M'')"
    using \<open>link_wf_3M M M' M''\<close> link_wf_def link_wf_3M_def
    by fastforce
  have wf: "link_wf M M'" 
    using \<open>link_wf_3M M M' M''\<close> 
    by simp 
  have  "((M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M''), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'"
    apply(rule link_exec_aux)
     apply(rule \<open>(M \<circ>\<^bsub>l\<^esub> M'), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'\<close>)
    using \<open>(link_wf_3M M M' M'')\<close> link_wf_3M_dest 
    by blast    
  from this wf link_assoc
  have b: "(M \<circ>\<^bsub>l\<^esub> (M' \<circ>\<^bsub>l\<^esub> M'')), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'"
    by metis   
  have "dom (M' \<circ>\<^bsub>l\<^esub> M'') = dom M' \<union> dom M''" 
    by (simp add: \<open>link_wf_3M M M' M''\<close>)
  hence c: "this_class_lookup \<sigma> = Some c \<and> c \<in> dom (M' \<circ>\<^bsub>l\<^esub> M'')" 
    using internal_exec_first_step
    by blast
  from a b c internal_exec_first_step
  show ?case 
    using internal_exec.internal_exec_first_step 
    by blast
next
  case (internal_exec_more_steps  \<sigma> tr \<sigma>' \<sigma>'' c)
  have a: "M;M' \<circ>\<^bsub>l\<^esub> M'',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>' "
    using \<open>link_wf_3M M M' M'' \<Longrightarrow> M;M' \<circ>\<^bsub>l\<^esub> M'',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>'\<close>
          and \<open>link_wf_3M M M' M''\<close> 
    by simp
  have asm: "M \<circ>\<^bsub>l\<^esub> (M' \<circ>\<^bsub>l\<^esub> M'') = (M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M''" 
    by (metis internal_exec_more_steps.prems 
        link_assoc link_wf_3M_dest(1))
  have "((M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M''), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>'' "
    apply (rule link_exec_aux)
     apply (rule \<open>(M \<circ>\<^bsub>l\<^esub> M'), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''\<close>)
    using \<open>link_wf_3M M M' M''\<close> link_wf_3M_dest 
    by blast
  from this and asm
  have b: "(M \<circ>\<^bsub>l\<^esub> (M' \<circ>\<^bsub>l\<^esub> M'')), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''" 
    by simp
  have c: "this_class_lookup \<sigma>'' = Some c \<and> (c \<in> dom M)" 
    using internal_exec_more_steps 
    by simp
  from a b c internal_exec.internal_exec_more_steps
  show ?case 
    by simp
qed

lemma internal_linking_2_aux: 
  "M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>' \<Longrightarrow> link_wf_3M M M' M''\<Longrightarrow> 
  (M \<circ>\<^bsub>l\<^esub> M''); M', \<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>'"
proof (induction rule: internal_exec.induct)
  case (internal_exec_first_step \<sigma> \<sigma>' c c')
  have a: "link_wf (M \<circ>\<^bsub>l\<^esub> M'') M'" 
    using \<open>link_wf_3M M M' M''\<close> 
    by (fastforce simp add: link_wf_def link_wf_3M_def)
  have " M\<circ>\<^bsub>l\<^esub> M'' = M''\<circ>\<^bsub>l\<^esub> M "  
    using \<open>link_wf_3M M M' M''\<close> link_commute 
    by blast
  hence "(M\<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M' =  M''\<circ>\<^bsub>l\<^esub> (M \<circ>\<^bsub>l\<^esub> M')" 
    using \<open>link_wf_3M M M' M''\<close> link_wf_3M_def link_wf_def 
        internal_exec_first_step.hyps(1) 
        internal_exec_first_step.prems 
        link_assoc link_commute link_wf_3M_dest(2) 
        link_wf_3M_dest(3) link_wf_3M_dest(4)
    by metis
  hence "(M\<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M' = (M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub>M''"
    by (simp add: \<open>link_wf_3M M M' M''\<close>)
  hence asm: "(M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M'' = (M\<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M'" 
    by simp
  have "((M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M''), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'"
    apply (rule link_exec_aux)
     apply (rule \<open>(M \<circ>\<^bsub>l\<^esub> M'), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'\<close>)
    using internal_exec_first_step 
    by blast
  from this and asm
  have b: "((M \<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M'), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'" 
    by simp 
  have c: "this_class_lookup \<sigma> = Some c \<and> (c \<in> dom M') "
    using internal_exec_first_step 
    by simp
  have d: "this_class_lookup \<sigma>' = Some c' \<and> 
            (c' \<in> dom (M \<circ>\<^bsub>l\<^esub> M''))" 
    using internal_exec_first_step 
    by simp  
  from a b c d  internal_exec_first_step 
  show ?case
    using internal_exec.internal_exec_first_step 
    by simp 
next
  case (internal_exec_more_steps  \<sigma> tr \<sigma>' \<sigma>'' c)
  from \<open>(link_wf_3M M M' M'') \<Longrightarrow> 
        (M \<circ>\<^bsub>l\<^esub> M'');M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>'\<close>
        and \<open>(link_wf_3M M M' M'')\<close>  
  have a: "(M \<circ>\<^bsub>l\<^esub> M'');M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>'" 
    by simp
  have "M \<circ>\<^bsub>l\<^esub> M'' = M''\<circ>\<^bsub>l\<^esub> M "  
    using \<open>link_wf_3M M M' M''\<close> link_commute 
    by blast
  hence "(M\<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M' =  M''\<circ>\<^bsub>l\<^esub> (M \<circ>\<^bsub>l\<^esub> M')" 
    using \<open>link_wf_3M M M' M''\<close> link_wf_3M_def link_wf_def 
    by (metis Int_Un_distrib Un_Int_crazy Un_Int_distrib 
        Un_commute distrib_imp2 inf.right_idem inf_commute 
        inf_sup_absorb internal_exec_more_steps.prems link_assoc 
        link_commute link_dom link_wf_3M_dest(3) link_wf_3M_dest(4) 
        sup.left_commute sup_assoc sup_bot.left_neutral 
        sup_bot.right_neutral sup_idem sup_inf_distrib1)
  hence "(M\<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M' = (M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub>M''"
    by (simp add: \<open>link_wf_3M M M' M''\<close>)
  hence asm: "(M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M'' = (M\<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M'" 
    by simp
  have "((M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M''), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''"
    apply (rule link_exec_aux)
     apply (rule \<open>(M \<circ>\<^bsub>l\<^esub> M'), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''\<close>)
    using \<open>link_wf_3M M M' M''\<close> 
    by blast
  from this and asm  
  have b: "((M \<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M'), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''" 
    by simp
  have c: "this_class_lookup \<sigma>'' = Some c \<and> 
          (c \<in> dom (M \<circ>\<^bsub>l\<^esub> M''))"
    using internal_exec_more_steps 
    by simp
  from a b c internal_exec.internal_exec_more_steps  
  show ?case  
    by simp
qed
(*using internal_linking1 to prove the lemma *)
(* M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'  implies M; (M' \<circ>\<^bsub>l\<^esub> M''), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'  *)
lemma visible_exec_linking_1_aux:
  "\<lbrakk>(M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'); (link_wf_3M M M' M'')\<rbrakk> \<Longrightarrow> 
    M; (M' \<circ>\<^bsub>l\<^esub> M''), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'"
proof (induction rule: visible_exec.induct)
  case (visible_exec_intro M M' \<sigma> tr \<sigma>' \<sigma>'' c)
  have a: "M; (M' \<circ>\<^bsub>l\<^esub> M''), \<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>'"  
    using \<open> M; M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>'\<close> 
    by (simp add: visible_exec_intro internal_linking_1_aux)
  have asm: "M \<circ>\<^bsub>l\<^esub> (M' \<circ>\<^bsub>l\<^esub> M'') = (M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M''" 
    by (metis link_assoc link_wf_3M_dest(1) 
          visible_exec_intro.prems)
  have "((M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M''), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>'' "
    apply (rule link_exec_aux)
     apply (rule \<open>(M \<circ>\<^bsub>l\<^esub> M'), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''\<close>)
    using \<open>link_wf_3M M M' M''\<close> link_wf_3M_dest 
    by blast
  from this and asm
  have b: "(M \<circ>\<^bsub>l\<^esub> (M' \<circ>\<^bsub>l\<^esub> M'')), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''" by simp
  have c: "this_class_lookup \<sigma>'' = Some c \<and> 
          ( c \<in> dom (M' \<circ>\<^bsub>l\<^esub> M''))"
    using \<open>this_class_lookup \<sigma>'' = Some c\<close> and \<open>c \<in> dom M'\<close> 
    by simp
  from a b c show ?case
    using visible_exec.visible_exec_intro 
    by simp
qed
(*using internal_linking2 to prove the lemma *)
(*Lemma 4.3b: M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'  implies (M \<circ>\<^bsub>l\<^esub> M''); M', \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'  *)
lemma visible_exec_linking_2_aux:
  "\<lbrakk>(M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'); (link_wf_3M M M' M'')\<rbrakk> \<Longrightarrow> 
    (M \<circ>\<^bsub>l\<^esub> M''); M', \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'"
proof (induction rule: visible_exec.induct)
  case (visible_exec_intro M M' \<sigma> tr \<sigma>' \<sigma>'' c)
  have a: "(M \<circ>\<^bsub>l\<^esub> M'');M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>'" 
    using \<open>M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>'\<close>
    by (simp add: \<open>link_wf_3M M M' M''\<close> internal_linking_2_aux)
  have "M \<circ>\<^bsub>l\<^esub> M'' = M'' \<circ>\<^bsub>l\<^esub> M"
    using link_commute visible_exec_intro 
    by auto
  hence "(M\<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M' =  M''\<circ>\<^bsub>l\<^esub> (M \<circ>\<^bsub>l\<^esub> M')" 
    using \<open>link_wf_3M M M' M''\<close> link_wf_3M_def link_wf_def 
    by auto
  hence "(M\<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M' = (M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub>M''"
    by (simp add: \<open>link_wf_3M M M' M''\<close>)
  hence asm:  "(M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M'' = (M\<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M'" 
    by simp
  have "((M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M''), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''"
    apply (rule link_exec_aux)
     apply (rule \<open>(M \<circ>\<^bsub>l\<^esub> M'), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''\<close>)
    using \<open>link_wf_3M M M' M''\<close> 
    by blast
  from this and asm 
  have b: "((M \<circ>\<^bsub>l\<^esub> M'') \<circ>\<^bsub>l\<^esub> M'), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>''" 
    by simp
  have c: "this_class_lookup \<sigma>'' = Some c \<and> c \<in> dom M'"
    using \<open>this_class_lookup \<sigma>'' = Some c\<close> and \<open>c \<in> dom M'\<close> 
    by simp 
  from a b c visible_exec.visible_exec_intro 
  show ?case 
    by simp
qed
section\<open>Technical Lemmas supporting Adaptation \label{Adaptation_appendix}\<close>
(*text\<open>We also give some definitions and lemmas supporting the definitions @{term fresh_idents} and @{term cont_subst_list},
such as @{term stmt_subst}, a function returns statement with every occurrence of identifiers replaced by other identifiers.\<close>*)
(* v[y/x] for an identifier v *)
definition 
ident_subst :: "Identifier \<Rightarrow> Identifier  \<Rightarrow> Identifier \<Rightarrow> Identifier" 
  where
"ident_subst x y v = (if v = x then y else v)"
(* s[y/x]: statement s with every occurrence of x replaced by y *)
fun 
stmt_subst :: "Stmt \<Rightarrow> Identifier \<Rightarrow> Identifier \<Rightarrow> Stmt" 
  where
"stmt_subst (AssignToField f v) x y = 
                (AssignToField f (ident_subst x y v))" |
"stmt_subst (ReadFromField v f) x y = 
                (ReadFromField (ident_subst x y v) f)" |
"stmt_subst (MethodCall v v' m vs) x y = 
    (MethodCall (ident_subst x y v) (ident_subst x y v') m (map (ident_subst x y) vs))" |
"stmt_subst (NewObject v c vs) x y = 
    (NewObject (ident_subst x y v) c (map (ident_subst x y) vs))" |
"stmt_subst (Return v) x y = 
    (Return (ident_subst x y v))"

fun 
stmt_idents :: "Stmt \<Rightarrow> Identifier set" 
  where
"stmt_idents (AssignToField f v) = {v}" |
"stmt_idents (ReadFromField v f) = {v}" |
"stmt_idents (MethodCall v v' m vs) = {v,v'} \<union> (set vs)" |
"stmt_idents (NewObject v c vs) = {v} \<union> (set vs)" |
"stmt_idents (Return v) = {v}"

lemma stmt_subst_idents:
  "stmt_idents (stmt_subst s x y) = 
   ((stmt_idents s - {x}) \<union> (if x \<in> stmt_idents s then {y} else {}))"
  by (induction rule: stmt_idents.induct, 
      auto simp: ident_subst_def split: if_splits)

fun 
stmts_subst :: "Stmts \<Rightarrow> Identifier \<Rightarrow> Identifier \<Rightarrow> Stmts" 
  where
"stmts_subst (SingleStmt s) x y = 
             (SingleStmt (stmt_subst s x y))" |
"stmts_subst (Seq s1 s2) x y = 
             (Seq (stmt_subst s1 x y) (stmts_subst s2 x y))"

fun 
stmts_idents :: "Stmts \<Rightarrow> Identifier set" 
  where
"stmts_idents (SingleStmt s) = (stmt_idents s)" |
"stmts_idents (Seq s1 s2) = (stmt_idents s1 \<union> (stmts_idents s2))"

lemma stmts_subst_idents:
  "stmts_idents (stmts_subst s x y) = 
   ((stmts_idents s - {x}) \<union> (if x \<in> stmts_idents s then {y} else {}))"
  by (induction rule: stmts_subst.induct, 
      auto simp: stmt_subst_idents)

fun 
stmts_subst_list :: "Stmts \<Rightarrow> Identifier list \<Rightarrow> Identifier list \<Rightarrow> Stmts" 
  where
"stmts_subst_list s (v#vs) (v'#vs') = 
              (stmts_subst_list (stmts_subst s v v') vs vs')" |
"stmts_subst_list s (v#vs) [] = undefined" |
"stmts_subst_list s [] (v'#vs') = undefined" | 
"stmts_subst_list s [] [] = s"

(* well-formed for stmts_subst_list *) 
definition 
stmts_subst_list_wf :: "Stmts \<Rightarrow> Identifier list \<Rightarrow> Identifier list \<Rightarrow> bool" 
  where
"stmts_subst_list_wf s vs vs' \<equiv>  (length vs = length vs') "

lemma stmts_list_idents:
 "stmts_subst_list_wf s vs vs'  \<Longrightarrow> 
  (stmts_idents (stmts_subst_list s vs vs') \<subseteq> 
  ((stmts_idents s - (set vs)) \<union> (set vs')))"
proof (induction rule: stmts_subst_list.induct)
  case (1 s v vs v' vs')
  then 
  have assm1: "stmts_subst_list_wf (stmts_subst s v v') vs vs'" 
    and assm2: "stmts_subst_list_wf (stmts_subst s v v') vs vs' \<Longrightarrow>
                stmts_idents (stmts_subst_list (stmts_subst s v v') vs vs')
                \<subseteq> stmts_idents (stmts_subst s v v') - set vs \<union> set vs'"
     apply (simp add: stmts_subst_list_wf_def)
    by (simp add: "1.IH")
  from assm1 and assm2 
  have assm3: "stmts_idents (stmts_subst_list (stmts_subst s v v') vs vs')
               \<subseteq> stmts_idents (stmts_subst s v v') - set vs \<union> set vs'"  
    by blast
  hence assm4: "stmts_idents (stmts_subst_list s (v # vs) (v' # vs')) = 
        stmts_idents (stmts_subst_list (stmts_subst s v v') vs vs')"
    by auto
  from assm1 assm2 assm3 assm4 
  have assm5: "stmts_idents (stmts_subst s v v') - set vs \<union> set vs'  
               \<subseteq> (stmts_idents s - set (v # vs) \<union> set (v' # vs'))"
    using stmts_subst_idents 
    by auto
  from  assm1 assm2 assm3 assm4 assm5
  have assm6: "stmts_idents (stmts_subst_list s (v # vs) (v' # vs')) 
               \<subseteq> (stmts_idents s - set (v # vs) \<union> set (v' # vs'))" 
    by blast
  thus ?case 
    by auto
next
  case (2 s v vs)
  thus ?case 
    by ( auto simp add: stmts_subst_list_wf_def)    
next
  case (3 s v' vs')
  thus ?case 
    by ( auto simp add: stmts_subst_list_wf_def)
next
  case (4 s)
  thus ?case 
    by simp
qed
text\<open>The @{term "fresh_idents X xs"} is used to generate a list of fresh identifiers 
where none of the new identifiers appear in @{term X} or @{term xs}. \<close>
primrec 
fresh_idents :: "Identifier set \<Rightarrow> Identifier list \<Rightarrow> Identifier list" 
  where
"fresh_idents X [] = []" |
"fresh_idents X (x#xs)  = (let v = fresh_nat (X \<union> (set (x#xs))) in 
                          (v # (fresh_idents (X \<union> {v}) xs)))"

lemma fresh_idents_length [simp]:
"length (fresh_idents X xs) = length xs"
  apply(induction xs arbitrary: X)
   apply clarsimp+
  by(metis length_Cons)

(*need to have X \<noteq> {} because fresh_nat X = 0 when X = {} *)
lemma fresh_ident_greater:
  "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> fresh_nat X > Max X"
  unfolding Max_def If_def
  by (metis Max_def Max_less_iff fresh_nat_def 
      last_sorted_list_of_list_is_greatest le_imp_less_Suc)

(* TODO: clean up this proof, which currently resorts to sledgehammer-generated Isar *)
lemma fresh_idents_greater: 
  "finite X  \<Longrightarrow>  xs \<noteq> [] \<Longrightarrow> (\<forall>x \<in> set (fresh_idents X xs). x > Max (X \<union> set xs))"
  apply(induction xs arbitrary: X)
   apply simp
  apply (clarsimp simp: Let_def)
  apply (rule conjI)
  using fresh_ident_greater apply simp
  apply(rule conjI)
  using fresh_ident_greater apply auto[1]
  apply clarsimp
  apply(subgoal_tac "(insert a (X \<union> set xs)) \<noteq> {} \<and> finite (insert a (X \<union> set xs))")
  using fresh_ident_greater
proof -
  fix a :: nat and xsa :: "nat list" 
      and Xa :: "nat set" and x :: nat
  assume a1: 
    "x \<in> set (fresh_idents (insert (fresh_nat (insert a (Xa \<union> set xsa))) Xa) xsa)"
  assume a2: 
    "\<And>X. \<lbrakk>finite X; xsa \<noteq> []\<rbrakk> \<Longrightarrow> \<forall>x\<in>set (fresh_idents X xsa). \<forall>a\<in>X \<union> set xsa. a < x"
  assume a3: "finite Xa"
  assume a4: 
    "insert a (Xa \<union> set xsa) \<noteq> {} \<and> finite (insert a (Xa \<union> set xsa))"
  have f5: 
    "\<forall>n. n \<notin> set (fresh_idents (insert (fresh_nat (insert a (Xa \<union> set xsa))) Xa) xsa) \<or> 
        (\<forall>na. na \<notin> insert (fresh_nat (insert a (Xa \<union> set xsa))) Xa \<union> set xsa \<or> na < n)"
    using a3 a2 
    by (metis finite.insertI fresh_idents.simps(1) insert_not_empty 
        mk_disjoint_insert set_empty2)
  have f6: "\<forall>n N na. (n::nat) \<notin> N \<and> n \<noteq> na \<or> n \<in> insert na N"
by force
  hence "a < fresh_nat (insert a (Xa \<union> set xsa))"
    using a4 by (metis (no_types) Max_less_iff fresh_ident_greater)
  hence "a < x"
    using f5 a1 by fastforce
  thus "a < x \<and> (\<forall>n\<in>Xa \<union> set xsa. n < x)"
    using f6 f5 a1 by (metis (no_types) Un_insert_left)
next
  fix a xs X x
  show
  "\<lbrakk>\<And>X. \<lbrakk>finite X; xs \<noteq> []\<rbrakk> \<Longrightarrow> \<forall>x\<in>set (fresh_idents X xs). 
                          \<forall>a\<in>X \<union> set xs. a < x; finite X;
     x \<in> set (fresh_idents (insert (fresh_nat (insert a (X \<union> set xs))) X) xs);
        \<And>X. \<lbrakk>finite X; X \<noteq> {}\<rbrakk> \<Longrightarrow> Max X < fresh_nat X\<rbrakk>
       \<Longrightarrow> insert a (X \<union> set xs) \<noteq> {} \<and> finite (insert a (X \<union> set xs))"
    by blast
qed

lemma fresh_idents_empty: 
  "finite X \<Longrightarrow> (set (fresh_idents X xs) \<inter> (X \<union> set xs)) = {}"
proof-
  assume "finite X "
  hence "(\<forall>x\<in>set (fresh_idents X xs). x > Max (X \<union> set xs))" 
    by (metis empty_iff empty_set fresh_idents.simps(1) fresh_idents_greater)
  then 
  show "(set (fresh_idents X xs) \<inter> (X \<union> set xs)) = {}"
    by (meson Int_emptyI List.finite_set Max_ge \<open>finite X\<close> finite_UnI not_le)
qed

lemma fresh_idents_distinct [simp]:
  "finite X \<Longrightarrow> distinct (fresh_idents X xs)"
proof(induction xs arbitrary: X)
  case Nil
  thus ?case 
    by clarsimp
next
  case (Cons a xs)
  show ?case 
  proof (clarsimp simp: Let_def, rule conjI)
    show "fresh_nat (insert a (X \<union> set xs))
    \<notin> set (fresh_idents (insert (fresh_nat (insert a (X \<union> set xs))) X) xs)"
      using fresh_idents_empty Cons.prems contra_subsetD 
      by blast
  next
    show 
      "distinct (fresh_idents (insert (fresh_nat (insert a (X \<union> set xs))) X) xs)"
      using Cons fresh_idents_empty 
      by simp
  qed
qed

fun 
ident_subst_list :: 
  "Identifier \<Rightarrow> Identifier list \<Rightarrow> Identifier list \<Rightarrow> Identifier"
  where
"ident_subst_list x (v#vs) (v'#vs') = (ident_subst v v' x)" |
"ident_subst_list x (v#vs) [] = undefined" |
"ident_subst_list x [] (v'#vs') = undefined" | 
"ident_subst_list x [] [] = x"
end