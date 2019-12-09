(* Title:      Quadcopter Controller Verification
   Author:     Omar A. Jasim <oajasim1@sheffield.ac.uk>, Sandor M. Veres <s.veres@sheffield.ac.uk>
   Maintainer: Omar A. Jasim <oajasim1@sheffield.ac.uk>, Sandor M. Veres <s.veres@sheffield.ac.uk> 
*)

theory Drone_veri_2
imports  Complex_Main 
"Quaternions.Quaternions"
(*"~~/src/HOL/Probability/Probability" *)
"~~/src/HOL/Matrix_LP/Matrix"
"~~/src/HOL/Library/Function_Algebras"
(*"~~/src/HOL/Probability/Analysis"*)
(*"~~/src/HOL/Analysis/Finite_Cartesian_Product"*)
begin
sledgehammer_params [provers = cvc4 z3 spass e remote_vampire , smt_proofs=true]

(**************************************************************************************************)
text \<open>Time definition\<close>
(**************************************************************************************************)
definition T :: "real set"
  where "T ={t. t\<in>{0..\<infinity>} }" 

(**************************************************************************************************)
text \<open>Definitions of sets, positive-definite matrix, and positive-definite symmetric matrix\<close>
(**************************************************************************************************)
definition D3_vec_set :: "(real, 3) vec set"
  where "D3_vec_set ={d. (\<forall>i.\<forall>f.\<forall>t\<in>T.  d$i = f t)}"  

definition D6_vec_set :: "(real, 6) vec set"
  where "D6_vec_set ={a. (\<forall>i.\<forall>f.\<forall>t\<in>T.  a$i = f t)}" 

(*positive-definite matrix*)
definition "pos_def_3x3_matrix X = (\<exists>r. \<exists>M. M=X \<and> (r:: (real,3) vec) \<noteq>0 \<and> (r \<bullet> (M *v r))>0)"

definition "pos_def_6x6_matrix Y = (\<exists>r. \<exists>F. F=Y \<and> (r:: (real,6) vec) \<noteq>0 \<and> (r \<bullet> (F *v r))>0)"

(*from Sylvester theorem : a matrix is a positive definite and symmetric matrix iff its principle 
  minors is positive or its eginvalues are positive*)  
definition "pos_def_symmetric_matrix A = (pos_def_6x6_matrix A \<and> A = transpose(A) \<and> det(A)\<noteq>0  
      \<and> (A$1$1)>0 \<and> ((A$1$1)*(A$2$2) - (A$1$2)*(A$2$1))>0 \<and> 
      (\<exists>!(B:: ((real,3) vec,3) vec). B$1$1=A$1$1 \<and> B$2$1=A$2$1 \<and> B$3$1=A$3$1 \<and> B$1$2=A$1$2 \<and> 
      B$2$2=A$2$2 \<and> B$3$2=A$3$2 \<and> B$1$3=A$1$3 \<and> B$2$3=A$2$3  \<and> B$3$3=A$3$3 \<and> det(B)>0 )   \<and>
      (\<exists>!(C:: ((real,4) vec,4) vec). C$1$1=A$1$1 \<and> C$2$1=A$2$1 \<and> C$3$1=A$3$1 \<and> C$4$1=A$4$1 \<and> 
      C$1$2=A$1$2 \<and> C$2$2=A$2$2 \<and> C$3$2=A$3$2 \<and>  C$4$2=A$4$2 \<and> C$1$3=A$1$3 \<and> C$2$3=A$2$3  \<and> 
      C$3$3=A$3$3 \<and> C$4$3=A$4$3 \<and> C$1$4=A$1$4 \<and> C$2$4=A$2$4 \<and> C$3$4=A$3$4 \<and> C$4$4=A$4$4 \<and> 
      det(C)>0 ) \<and>  (\<exists>!(D:: ((real,5) vec,5) vec). D$1$1=A$1$1 \<and> D$2$1=A$2$1 \<and> D$3$1=A$3$1 \<and> 
      D$4$1=A$4$1 \<and> D$5$1=A$5$1 \<and> D$1$2=A$1$2 \<and> D$2$2=A$2$2 \<and> D$3$2=A$3$2 \<and> D$4$2=A$4$2 \<and>  
      D$5$2=A$5$2 \<and> D$1$3=A$1$3 \<and> D$2$3=A$2$3 \<and> D$3$3=A$3$3 \<and> D$4$3=A$4$3 \<and> D$5$3=A$5$3 \<and> 
      D$1$4=A$1$4 \<and> D$2$4=A$2$4 \<and> D$3$4=A$3$4 \<and> D$4$4=A$4$4 \<and> D$5$4=A$5$4 \<and> D$1$5=A$1$5 \<and> 
      D$2$5=A$2$5 \<and> D$3$5=A$3$5 \<and> D$4$5=A$4$5 \<and> D$5$5=A$5$5 \<and> det(D)>0 )  \<and> det(A)>0 )"

(**************************************************************************************************)
text \<open>Parameters definitions\<close>
(**************************************************************************************************)
definition"(ell :: real)=0.2" (*m*)    (*arm length*) 
definition"(k :: real)=0.00000012" (*N/(rad/sec)\<^sup>2*)
definition"(b :: real)=0.00000009" (*N.m/(rad/sec)\<^sup>2*)
definition"(H :: real)=1.2" 
definition"(\<sigma> :: real)=0.0000000000009" 
definition"(\<xi> :: real)=0.5" 
definition"(S :: real)=0.001"
definition"(D :: real)=0.001"
definition"(D\<^sub>b\<^sub>a\<^sub>r :: real)=0.002"
definition"(\<beta>\<^sub>m\<^sub>i\<^sub>n :: real)=170.5" 
definition"(\<beta>\<^sub>m\<^sub>a\<^sub>x :: real)=173" 
definition"(k\<^sub>q\<^sub>0 :: real)=0.01" 
definition"(I\<^sub>x :: real)=0.005831" 
definition"(I\<^sub>y :: real)=0.005831" 
definition"(I\<^sub>z :: real)=0.01166" 
definition"(\<omega>\<^sub>m\<^sub>a\<^sub>x :: real)=707.1068" (*rad/sec*)

(**************************************************************************************************)
text \<open>Euler angles limits / Euler vector\<close>
(**************************************************************************************************)
definition "Euler_ang \<phi> \<theta> \<psi>  = (\<forall>t. t\<in>T \<and> -pi/2 < (\<phi> :: real\<Rightarrow>real)(t) \<and> \<phi>(t) < pi/2 
                                       \<and> -pi/2 < (\<theta> :: real\<Rightarrow>real)(t) \<and> \<theta>(t) < pi/2 \<and> (\<psi> :: real\<Rightarrow>real)(t) \<in> \<real>)"

definition "Euler_vec \<eta> \<phi> \<theta> \<psi> = (\<forall>t. t\<in>T \<and> Euler_ang \<phi> \<theta> \<psi> \<and> \<eta>\<in>D3_vec_set \<and>
                                 \<eta>$1=\<phi>(t) \<and> \<eta>$2=\<theta>(t) \<and> \<eta>$3=\<psi>(t))"


(**************************************************************************************************)
text \<open>Matrices definitions\<close>
(**************************************************************************************************)
(* J uncertain matrix -  Eq. 4*)
definition "J_mat J \<phi> \<theta> \<psi> = (\<forall>t. t\<in>T \<and> pos_def_3x3_matrix J \<and> invertible J \<and>  
                          J**matrix_inv(J) = mat 1 \<and> norm(matrix_inv(J)) > 0 \<and> 
                       \<beta>\<^sub>m\<^sub>i\<^sub>n \<le> norm(matrix_inv(J)) \<and> norm(matrix_inv(J)) \<le> \<beta>\<^sub>m\<^sub>a\<^sub>x \<and> Euler_ang \<phi> \<theta> \<psi> \<and>
                     J$1$1 = I\<^sub>x           \<and> J$2$1 = 0                               \<and> J$3$1 = -I\<^sub>x * sin(\<theta>(t)) \<and>
                     J$1$2 = 0            \<and> J$2$2 =(I\<^sub>y* (cos(\<phi>(t)))\<^sup>2 + I\<^sub>z * (sin(\<phi>(t)))\<^sup>2) \<and> J$3$2 = (I\<^sub>y-I\<^sub>z)* cos(\<phi>(t))* sin(\<phi>(t))* cos(\<theta>(t)) \<and>
                     J$1$3 = -I\<^sub>x * sin(\<theta>(t)) \<and> J$2$3 = (I\<^sub>y-I\<^sub>z)* cos(\<phi>(t))* sin(\<phi>(t))* cos(\<theta>(t)) \<and> J$3$3 = I\<^sub>x*(sin(\<theta>(t)))\<^sup>2 +I\<^sub>y*(sin(\<phi>(t)))\<^sup>2*(cos(\<theta>(t)))\<^sup>2 + I\<^sub>z*(cos(\<phi>(t)))\<^sup>2*(cos(\<theta>(t)))\<^sup>2)"

(* J\<^sub>h\<^sub>a\<^sub>t the assumed  matrix values*)
definition "J\<^sub>h\<^sub>a\<^sub>t_mat (J\<^sub>h\<^sub>a\<^sub>t :: ((real, 3) vec, 3) vec) \<phi> \<theta> \<psi> = (\<forall>t. t\<in>T \<and> pos_def_3x3_matrix J\<^sub>h\<^sub>a\<^sub>t \<and>
                     transpose J\<^sub>h\<^sub>a\<^sub>t = J\<^sub>h\<^sub>a\<^sub>t    \<and> invertible J\<^sub>h\<^sub>a\<^sub>t \<and> Euler_ang \<phi> \<theta> \<psi> \<and>
                     J\<^sub>h\<^sub>a\<^sub>t$1$1 = I\<^sub>x              \<and> J\<^sub>h\<^sub>a\<^sub>t$2$1 = 0                                        \<and> J\<^sub>h\<^sub>a\<^sub>t$3$1 = -I\<^sub>x * sin(\<theta>(t)) \<and>
                     J\<^sub>h\<^sub>a\<^sub>t$1$2 = 0               \<and> J\<^sub>h\<^sub>a\<^sub>t$2$2 =(I\<^sub>y* (cos(\<phi>(t)))\<^sup>2 + I\<^sub>z * (sin(\<phi>(t)))\<^sup>2)    \<and> J\<^sub>h\<^sub>a\<^sub>t$3$2 = (I\<^sub>y-I\<^sub>z)* cos(\<phi>(t))* sin(\<phi>(t))* cos(\<theta>(t)) \<and>
                     J\<^sub>h\<^sub>a\<^sub>t$1$3 = -I\<^sub>x * sin(\<theta>(t)) \<and> J\<^sub>h\<^sub>a\<^sub>t$2$3 = (I\<^sub>y-I\<^sub>z)* cos(\<phi>(t))* sin(\<phi>(t))* cos(\<theta>(t)) \<and> J\<^sub>h\<^sub>a\<^sub>t$3$3 = I\<^sub>x*(sin(\<theta>(t)))\<^sup>2 +I\<^sub>y*(sin(\<phi>(t)))\<^sup>2*(cos(\<theta>(t)))\<^sup>2 + I\<^sub>z*(cos(\<phi>(t)))\<^sup>2*(cos(\<theta>(t)))\<^sup>2)"

(* K\<^sub>\<eta> matrix values*)
definition "K\<^sub>\<eta>_mat (K\<^sub>\<eta> :: ((real, 3) vec, 3) vec)  = (pos_def_3x3_matrix K\<^sub>\<eta> \<and>
                   K\<^sub>\<eta>$1$1 = 17.5 \<and> K\<^sub>\<eta>$2$1 = 0     \<and> K\<^sub>\<eta>$3$1 = 0 \<and>
                   K\<^sub>\<eta>$1$2 = 0    \<and> K\<^sub>\<eta>$2$2 = 17.5  \<and> K\<^sub>\<eta>$3$2 = 0 \<and>
                   K\<^sub>\<eta>$1$3 = 0    \<and> K\<^sub>\<eta>$2$3 = 0     \<and> K\<^sub>\<eta>$3$3 = 1.8)"

(* K\<^sub>r matrix values*)
definition "K\<^sub>r_mat (K\<^sub>r :: ((real, 3) vec, 3) vec)  = (pos_def_3x3_matrix K\<^sub>r \<and> 
                   K\<^sub>r$1$1 = 0.004  \<and> K\<^sub>r$2$1 = 0     \<and> K\<^sub>r$3$1 = 0 \<and>
                   K\<^sub>r$1$2 = 0      \<and> K\<^sub>r$2$2 = 0.004 \<and> K\<^sub>r$3$2 = 0 \<and>
                   K\<^sub>r$1$3 = 0      \<and> K\<^sub>r$2$3 = 0     \<and> K\<^sub>r$3$3 = 0.4826)"

(* W matrix values Eq. 2 *)
definition "W_mat (W ::((real, 3)vec,3)vec) \<phi> \<theta> \<psi> = (\<forall>t. t\<in>T \<and> Euler_ang \<phi> \<theta> \<psi> \<and>
            ((W$1)$1) = 1 \<and> ((W$2)$1) = 0           \<and> ((W$3)$1) = - sin(\<theta>(t))            \<and>
            ((W$1)$2) = 0 \<and> ((W$2)$2) = cos(\<phi>(t))   \<and> ((W$3)$2) = cos(\<theta>(t)) * sin(\<phi>(t)) \<and>
            ((W$1)$3) = 0 \<and> ((W$2)$3) = - sin(\<phi>(t)) \<and> ((W$3)$3) = cos(\<theta>(t)) * cos(\<phi>(t)) )"

(* A matrix values Eq. 23*)
definition "A_mat (A :: ((real, 6) vec,6) vec)  = 
            (A$1$1=0      \<and>  A$2$1=0     \<and>  A$3$1=0    \<and>  A$4$1=1      \<and>  A$5$1=0      \<and>  A$6$1=0 \<and>
             A$1$2=0      \<and>  A$2$2=0     \<and>  A$3$2=0    \<and>  A$4$2=0      \<and>  A$5$2=1      \<and>  A$6$2=0 \<and>
             A$1$3=0      \<and>  A$2$3=0     \<and>  A$3$3=0    \<and>  A$4$3=0      \<and>  A$5$3=0      \<and>  A$6$3=1 \<and>
             A$1$4=-17.5  \<and>  A$2$4=0     \<and>  A$3$4=0    \<and>  A$4$4=-0.004 \<and>  A$5$4=0      \<and>  A$6$4=0 \<and>
             A$1$5=0      \<and>  A$2$5=-17.5 \<and>  A$3$5=0    \<and>  A$4$5=0      \<and>  A$5$5=-0.004 \<and>  A$6$5=0 \<and>
             A$1$6=0      \<and>  A$2$6=0     \<and>  A$3$6=-1.8 \<and>  A$4$6=0      \<and>  A$5$6=0      \<and>  A$6$6=-0.4826)"

(* B matrix values Eq. 23 *)
definition "B_mat (B :: ((real, 3) vec, 6) vec)  = 
            (B$1$1=0     \<and>  B$2$1=0     \<and>  B$3$1=0 \<and>    
             B$1$2=0     \<and>  B$2$2=0     \<and>  B$3$2=0 \<and>    
             B$1$3=0     \<and>  B$2$3=0     \<and>  B$3$3=0 \<and>    
             B$1$4=1     \<and>  B$2$4=0     \<and>  B$3$4=0 \<and>    
             B$1$5=0     \<and>  B$2$5=1     \<and>  B$3$5=0 \<and>    
             B$1$6=0     \<and>  B$2$6=0     \<and>  B$3$6=1 )"

(* P matrix values Eq. 41*)
definition "P_mat (P :: ((real, 6) vec,6) vec)  = (pos_def_symmetric_matrix P \<and>
             P$1$1 = 0.000000000009 \<and>  P$2$1=0              \<and>  P$3$1=0               \<and>  P$4$1=0            \<and>  P$5$1=0            \<and>  P$6$1=0 \<and>
             P$1$2 = 0              \<and>  P$2$2=0.000000000009 \<and>  P$3$2=0               \<and>  P$4$2=0            \<and>  P$5$2=0            \<and>  P$6$2=0 \<and>
             P$1$3 = 0              \<and>  P$2$3=0              \<and>  P$3$3=0.000000005     \<and>  P$4$3=0            \<and>  P$5$3=0            \<and>  P$6$3=0 \<and>
             P$1$4 = 0              \<and>  P$2$4=0              \<and>  P$3$4=0               \<and>  P$4$4=0.00000003   \<and>  P$5$4=0            \<and>  P$6$4=0 \<and>
             P$1$5 = 0              \<and>  P$2$5=0              \<and>  P$3$5=0               \<and>  P$4$5=0            \<and>  P$5$5=0.00000003   \<and>  P$6$5=0 \<and>
             P$1$6 = 0              \<and>  P$2$6=0              \<and>  P$3$6=0               \<and>  P$4$6=0            \<and>  P$5$6=0            \<and>  P$6$6=0.0008)"

(* Q matrix values Eq. 42*)
definition "Q_mat (Q :: ((real, 6) vec,6) vec)  = (pos_def_symmetric_matrix Q \<and>
             Q$1$1 = 0.0000002 \<and>  Q$2$1= 0         \<and>  Q$3$1= 0       \<and>  Q$4$1= 0         \<and>  Q$5$1= 0         \<and>  Q$6$1=0 \<and>
             Q$1$2 = 0         \<and>  Q$2$2= 0.0000002 \<and>  Q$3$2= 0       \<and>  Q$4$2= 0         \<and>  Q$5$2= 0         \<and>  Q$6$2=0 \<and>
             Q$1$3 = 0         \<and>  Q$2$3= 0         \<and>  Q$3$3= 0.00046 \<and>  Q$4$3= 0         \<and>  Q$5$3= 0         \<and>  Q$6$3=0 \<and>
             Q$1$4 = 0         \<and>  Q$2$4= 0         \<and>  Q$3$4= 0       \<and>  Q$4$4= 0.0000038 \<and>  Q$5$4= 0         \<and>  Q$6$4=0 \<and>
             Q$1$5 = 0         \<and>  Q$2$5= 0         \<and>  Q$3$5= 0       \<and>  Q$4$5= 0         \<and>  Q$5$5= 0.0000038 \<and>  Q$6$5=0 \<and>
             Q$1$6 = 0         \<and>  Q$2$6= 0         \<and>  Q$3$6= 0       \<and>  Q$4$6= 0         \<and>  Q$5$6= 0         \<and>  Q$6$6=0.00082)"
(*################################################################################################*)

(**************************************************************************************************)
section \<open>Quadcopter attitude dynamics\<close>
(**************************************************************************************************)

(* \<tau> vector equation *)
definition "torq_fun \<tau> = ((\<exists> \<omega>\<^sub>1 \<omega>\<^sub>2 \<omega>\<^sub>3 \<omega>\<^sub>4. \<bar>\<omega>\<^sub>1\<bar><\<omega>\<^sub>m\<^sub>a\<^sub>x \<and> \<bar>\<omega>\<^sub>2\<bar><\<omega>\<^sub>m\<^sub>a\<^sub>x \<and> \<bar>\<omega>\<^sub>3\<bar><\<omega>\<^sub>m\<^sub>a\<^sub>x \<and> \<bar>\<omega>\<^sub>4\<bar><\<omega>\<^sub>m\<^sub>a\<^sub>x \<and> 
                         \<tau> \<in> D3_vec_set \<and> 
                         \<tau>$1= ell*k*(\<omega>\<^sub>2\<^sup>2 - \<omega>\<^sub>4\<^sup>2)  \<and>
                         \<tau>$2= ell*k*(-\<omega>\<^sub>1\<^sup>2 + \<omega>\<^sub>3\<^sup>2) \<and>
                         \<tau>$3= b*(-\<omega>\<^sub>1\<^sup>2 + \<omega>\<^sub>2\<^sup>2 - \<omega>\<^sub>3\<^sup>2 + \<omega>\<^sub>4\<^sup>2) ))"

(* C matrix equation Eq. 6*)
definition "C_mat (C :: ((real, 3) vec,3) vec) \<phi> \<theta> \<psi>  = (\<forall>t.\<exists> \<phi>' \<theta>' \<psi>'. t\<in>T \<and> Euler_ang \<phi> \<theta> \<psi> \<and> 
             (((\<lambda>t. \<phi>(t)) has_derivative (\<lambda>t. \<phi>'(t))) (at t within T)) \<and>
             (((\<lambda>t. \<theta>(t)) has_derivative (\<lambda>t. \<theta>'(t))) (at t within T)) \<and>
             (((\<lambda>t. \<psi>(t)) has_derivative (\<lambda>t. \<psi>'(t))) (at t within T)) \<and> 
             C$1$1 = 0 \<and>  
             C$2$1= ((I\<^sub>y - I\<^sub>z)*((\<theta>'(t)*cos(\<phi>(t))* sin(\<phi>(t))) + (\<psi>'(t)*(sin(\<phi>(t)))^2 * cos(\<theta>(t))) )) + (((I\<^sub>z-I\<^sub>y)* (\<psi>'(t)*(cos(\<phi>(t)))^2 *cos(\<theta>(t))))- ( I\<^sub>x*\<psi>'(t)*cos(\<theta>(t)) ))  \<and>  
             C$3$1= (I\<^sub>z-I\<^sub>y)* (\<psi>'(t)* cos(\<phi>(t))* sin(\<phi>(t))* (cos(\<theta>(t)))^2)  \<and>    
             C$1$2 = ((I\<^sub>z - I\<^sub>y)*((\<theta>'(t)*cos(\<phi>(t))* sin(\<phi>(t))) + (\<psi>'(t)* sin(\<phi>(t)) * cos(\<theta>(t))) ))+ ((I\<^sub>y-I\<^sub>z)* (\<psi>'(t)*(cos(\<phi>(t)))^2 *cos(\<theta>(t)))) +  ( I\<^sub>x*\<psi>'(t)*cos(\<theta>(t))  )  \<and>  
             C$2$2=((I\<^sub>z - I\<^sub>y)* (\<phi>'(t)*cos(\<phi>(t))* sin(\<phi>(t)))) \<and>  
             C$3$2= (-I\<^sub>x*\<psi>'(t)* sin(\<theta>(t))*cos(\<theta>(t)))  +  (I\<^sub>y*\<psi>'(t)*(sin(\<phi>(t)))^2* sin(\<theta>(t))*cos(\<theta>(t))) + (I\<^sub>z*\<psi>'(t)*(cos(\<phi>(t)))^2* sin(\<theta>(t))*cos(\<theta>(t)))   \<and>    
             C$1$3 = ((I\<^sub>y - I\<^sub>z)*  (\<psi>'(t)*(cos(\<theta>(t)))^2* sin(\<phi>(t))*cos(\<phi>(t))) )   -  (I\<^sub>x*\<theta>'(t)*cos(\<theta>(t))) \<and>  
             C$2$3= ((I\<^sub>z - I\<^sub>y)*  ((\<theta>'(t)*cos(\<phi>(t))* sin(\<phi>(t))* sin(\<theta>(t)))  +  (\<phi>'(t)*(sin(\<phi>(t)))^2*cos(\<theta>(t))) ) )+((I\<^sub>y - I\<^sub>z)*  (\<phi>'(t)*(cos(\<phi>(t)))^2*cos(\<theta>(t))) ) + ( I\<^sub>x* \<psi>'(t)* sin(\<theta>(t))*cos(\<theta>(t)) ) - (I\<^sub>y*\<psi>'(t)*(sin(\<phi>(t)))^2* sin(\<theta>(t))*cos(\<theta>(t))) \<and>  
             C$3$3= ( ((I\<^sub>y - I\<^sub>z)*  (\<phi>'(t)*cos(\<phi>(t))* sin(\<phi>(t))*(cos(\<theta>(t)))^2)) ) - (I\<^sub>y*\<theta>'(t)*(sin(\<phi>(t)))^2*cos(\<theta>(t))* sin(\<theta>(t))) - (I\<^sub>z*\<theta>'(t)*(cos(\<phi>(t)))^2*cos(\<theta>(t))* sin(\<theta>(t))) + (I\<^sub>x*\<theta>'(t)*cos(\<theta>(t))* sin(\<theta>(t))) )"
             


definition "C\<^sub>h\<^sub>a\<^sub>t_mat (C\<^sub>h\<^sub>a\<^sub>t :: ((real, 3) vec,3) vec) \<phi> \<theta> \<psi>  = (\<forall>t.\<exists> \<phi>' \<theta>' \<psi>'. t\<in>T \<and> Euler_ang \<phi> \<theta> \<psi> \<and> 
             (((\<lambda>t. \<phi>(t)) has_derivative (\<lambda>t. \<phi>'(t))) (at t within T)) \<and>
             (((\<lambda>t. \<theta>(t)) has_derivative (\<lambda>t. \<theta>'(t))) (at t within T)) \<and>
             (((\<lambda>t. \<psi>(t)) has_derivative (\<lambda>t. \<psi>'(t))) (at t within T)) \<and> 
             C\<^sub>h\<^sub>a\<^sub>t$1$1 = 0 \<and>  
             C\<^sub>h\<^sub>a\<^sub>t$2$1= ((I\<^sub>y - I\<^sub>z)*((\<theta>'(t)*cos(\<phi>(t))* sin(\<phi>(t))) + (\<psi>'(t)*(sin(\<phi>(t)))^2 * cos(\<theta>(t))) )) + (((I\<^sub>z-I\<^sub>y)* (\<psi>'(t)*(cos(\<phi>(t)))^2 *cos(\<theta>(t))))- ( I\<^sub>x*\<psi>'(t)*cos(\<theta>(t)) ))  \<and>  
             C\<^sub>h\<^sub>a\<^sub>t$3$1= (I\<^sub>z-I\<^sub>y)* (\<psi>'(t)* cos(\<phi>(t))* sin(\<phi>(t))* (cos(\<theta>(t)))^2)  \<and>    
             C\<^sub>h\<^sub>a\<^sub>t$1$2 = ((I\<^sub>z - I\<^sub>y)*((\<theta>'(t)*cos(\<phi>(t))* sin(\<phi>(t))) + (\<psi>'(t)* sin(\<phi>(t)) * cos(\<theta>(t))) ))+ ((I\<^sub>y-I\<^sub>z)* (\<psi>'(t)*(cos(\<phi>(t)))^2 *cos(\<theta>(t)))) +  ( I\<^sub>x*\<psi>'(t)*cos(\<theta>(t))  )  \<and>  
             C\<^sub>h\<^sub>a\<^sub>t$2$2=((I\<^sub>z - I\<^sub>y)* (\<phi>'(t)*cos(\<phi>(t))* sin(\<phi>(t)))) \<and>  
             C\<^sub>h\<^sub>a\<^sub>t$3$2= (-I\<^sub>x*\<psi>'(t)* sin(\<theta>(t))*cos(\<theta>(t)))  +  (I\<^sub>y*\<psi>'(t)*(sin(\<phi>(t)))^2* sin(\<theta>(t))*cos(\<theta>(t))) + (I\<^sub>z*\<psi>'(t)*(cos(\<phi>(t)))^2* sin(\<theta>(t))*cos(\<theta>(t)))   \<and>    
             C\<^sub>h\<^sub>a\<^sub>t$1$3 = ((I\<^sub>y - I\<^sub>z)*  (\<psi>'(t)*(cos(\<theta>(t)))^2* sin(\<phi>(t))*cos(\<phi>(t))) )   -  (I\<^sub>x*\<theta>'(t)*cos(\<theta>(t))) \<and>  
             C\<^sub>h\<^sub>a\<^sub>t$2$3= ((I\<^sub>z - I\<^sub>y)*  ((\<theta>'(t)*cos(\<phi>(t))* sin(\<phi>(t))* sin(\<theta>(t)))  +  (\<phi>'(t)*(sin(\<phi>(t)))^2*cos(\<theta>(t))) ) )+((I\<^sub>y - I\<^sub>z)*  (\<phi>'(t)*(cos(\<phi>(t)))^2*cos(\<theta>(t))) ) + ( I\<^sub>x* \<psi>'(t)* sin(\<theta>(t))*cos(\<theta>(t)) ) - (I\<^sub>y*\<psi>'(t)*(sin(\<phi>(t)))^2* sin(\<theta>(t))*cos(\<theta>(t))) \<and>  
             C\<^sub>h\<^sub>a\<^sub>t$3$3= ( ((I\<^sub>y - I\<^sub>z)*  (\<phi>'(t)*cos(\<phi>(t))* sin(\<phi>(t))*(cos(\<theta>(t)))^2)) ) - (I\<^sub>y*\<theta>'(t)*(sin(\<phi>(t)))^2*cos(\<theta>(t))* sin(\<theta>(t))) - (I\<^sub>z*\<theta>'(t)*(cos(\<phi>(t)))^2*cos(\<theta>(t))* sin(\<theta>(t))) + (I\<^sub>x*\<theta>'(t)*cos(\<theta>(t))* sin(\<theta>(t))) )"
             

(* attitude dynamics equation *)
definition "att_dyms \<tau> J C \<eta> \<phi> \<theta> \<psi> d = (\<forall>t\<in>T.\<forall> \<eta>' \<eta>''. (\<forall>\<eta>. \<eta>\<in>D3_vec_set) \<and> Euler_vec \<eta> \<phi> \<theta> \<psi> \<and>
                     (\<forall>i.((\<lambda>t. \<eta>$i) has_derivative (\<lambda>t. \<eta>'$i)) (at t within T)) \<and> 
                     (\<forall>i.((\<lambda>t. \<eta>'$i) has_derivative (\<lambda>t. \<eta>''$i)) (at t within T)) \<and>
                     J_mat J \<phi> \<theta> \<psi> \<and> C_mat C \<phi> \<theta> \<psi> \<and> \<tau> = J *v \<eta>'' + C *v \<eta>' + d)"

(*################################################################################################*)

(**************************************************************************************************)
section \<open>Control System Design\<close>
(**************************************************************************************************)

(* 1st and 2nd  derivative of \<eta> and \<eta>\<^sub>d Euler vector *)
definition "ddot_\<eta>_vec \<eta>\<^sub>d \<eta>\<^sub>d' \<eta>\<^sub>d'' \<phi>\<^sub>d \<theta>\<^sub>d \<psi>\<^sub>d = (\<forall>t\<in>T. \<exists> \<eta>\<^sub>d' \<eta>\<^sub>d''. Euler_vec \<eta>\<^sub>d \<phi>\<^sub>d \<theta>\<^sub>d \<psi>\<^sub>d \<and>
                                    ( \<forall>i.((\<lambda>t. \<eta>\<^sub>d$i) has_derivative (\<lambda>t. \<eta>\<^sub>d'$i)) (at t within T)) \<and>
                                    ( \<forall>i.((\<lambda>t. \<eta>\<^sub>d'$i) has_derivative (\<lambda>t. \<eta>\<^sub>d''$i)) (at t within T)))"

(*error e, e' and e'' definition Eq. 16 and 17*)
definition "error_vec e \<eta> \<eta>\<^sub>d \<phi> \<theta> \<psi> = (Euler_vec \<eta> \<phi> \<theta> \<psi> \<and>  e = \<eta>\<^sub>d - \<eta>)"

definition "dot_error_vec e e' \<eta> \<eta>\<^sub>d \<eta>' \<eta>\<^sub>d' \<phi> \<theta> \<psi> = (\<forall>t. error_vec e \<eta> \<eta>\<^sub>d \<phi> \<theta> \<psi> \<and>
                   (\<forall>i.((\<lambda>t. \<eta>$i) has_derivative (\<lambda>t. \<eta>'$i)) (at t within T)) \<and>
                   (\<forall>i.((\<lambda>t. \<eta>\<^sub>d$i) has_derivative (\<lambda>t. \<eta>\<^sub>d'$i)) (at t within T)) \<and>
                    e' = \<eta>\<^sub>d' - \<eta>')"

definition "ddot_error_vec e e' e'' \<eta> \<eta>' \<eta>'' \<eta>\<^sub>d \<eta>\<^sub>d' \<eta>\<^sub>d'' \<phi> \<theta> \<psi> \<phi>\<^sub>d \<theta>\<^sub>d \<psi>\<^sub>d = (\<forall>t. error_vec e \<eta> \<eta>\<^sub>d \<phi> \<theta> \<psi> \<and>
                   ddot_\<eta>_vec \<eta>\<^sub>d \<eta>\<^sub>d' \<eta>\<^sub>d'' \<phi>\<^sub>d \<theta>\<^sub>d \<psi>\<^sub>d \<and> ddot_\<eta>_vec \<eta> \<eta>' \<eta>'' \<phi> \<theta> \<psi> \<and>
                   (\<forall>i.((\<lambda>t. e$i) has_derivative (\<lambda>t. e'$i)) (at t within T)) \<and>
                   (\<forall>i.((\<lambda>t. e'$i) has_derivative (\<lambda>t. e''$i)) (at t within T)) \<and>
                    e'' = \<eta>\<^sub>d'' - \<eta>'')"

(*N and N\<^sub>h\<^sub>a\<^sub>t vectors definitions*)
definition "N_vec N C \<eta> \<eta>' \<phi> \<theta> \<psi> =(\<forall>t. Euler_vec \<eta> \<phi> \<theta> \<psi> \<and> C_mat C \<phi> \<theta> \<psi> \<and>
                             (\<forall>i.((\<lambda>t. \<eta>$i) has_derivative (\<lambda>t. \<eta>'$i)) (at t within T)) \<and>
                              N = C *v \<eta>')"

definition "N\<^sub>h\<^sub>a\<^sub>t_vec N\<^sub>h\<^sub>a\<^sub>t C\<^sub>h\<^sub>a\<^sub>t \<eta> \<phi> \<theta> \<psi> =(\<forall>t. \<exists> \<eta>'. Euler_vec \<eta> \<phi> \<theta> \<psi> \<and> C\<^sub>h\<^sub>a\<^sub>t_mat C\<^sub>h\<^sub>a\<^sub>t \<phi> \<theta> \<psi> \<and>
                             (\<forall>i.((\<lambda>t. \<eta>$i) has_derivative (\<lambda>t. \<eta>'$i)) (at t within T)) \<and>
                              N\<^sub>h\<^sub>a\<^sub>t = C\<^sub>h\<^sub>a\<^sub>t *v \<eta>')"

(* E vector definition*)
definition "E_vec (E:: (real,6)vec) \<eta> \<eta>' = (E$1 = \<eta>$1  \<and> E$2 = \<eta>$2  \<and> E$3 = \<eta>$3  \<and>
                                            E$4 = \<eta>'$1 \<and> E$5 = \<eta>'$2 \<and> E$6 = \<eta>'$3 )"

(*################################################################################################*)

(**************************************************************************************************)
subsection \<open>assumptions\<close>
(**************************************************************************************************)

(* assumption 1- Eq. 14 *)
definition "assump1 (d ::(real,3)vec) d\<^sub>h\<^sub>a\<^sub>t \<Delta>d = (\<Delta>d = d\<^sub>h\<^sub>a\<^sub>t - d \<and> norm(\<Delta>d) \<le> D \<and> norm(d)+D < D\<^sub>b\<^sub>a\<^sub>r)"

(* assumption 2 - Eq.15 *)
definition "assump2 (N ::(real,3)vec) N\<^sub>h\<^sub>a\<^sub>t \<Delta>N =  (\<Delta>N = N\<^sub>h\<^sub>a\<^sub>t - N \<and> norm(\<Delta>N) \<le> S)"

(* assumption 3 - Eqs.24 *)
definition "assump3_a \<eta>\<^sub>d'' = ((SUP t:T. norm(\<eta>\<^sub>d'')) < H)"

(* assumption 3 - Eqs.25-26 *)
definition "assump3_b J J\<^sub>h\<^sub>a\<^sub>t \<phi> \<theta> \<psi> = (J_mat J \<phi> \<theta> \<psi> \<and> J\<^sub>h\<^sub>a\<^sub>t_mat J\<^sub>h\<^sub>a\<^sub>t \<phi> \<theta> \<psi> \<and>
                                     norm(mat 1 - J\<^sub>h\<^sub>a\<^sub>t ** matrix_inv(J)) \<le> \<xi> \<and>
                                     \<beta>\<^sub>m\<^sub>i\<^sub>n \<le> norm(matrix_inv(J)) \<and> norm(matrix_inv(J)) \<le> \<beta>\<^sub>m\<^sub>a\<^sub>x)"

(*################################################################################################*)


(**************************************************************************************************)
subsection \<open>Controller definitions\<close>
(**************************************************************************************************)

(* u control input definition *)
definition "cont_u (u :: (real, 3) vec) \<eta>\<^sub>d'' K\<^sub>r K\<^sub>\<eta> e e'  = (u= \<eta>\<^sub>d'' + K\<^sub>r *v e' + K\<^sub>\<eta> *v e)"

(*v equation Eq. 19*)
definition "v_eq v u J J\<^sub>h\<^sub>a\<^sub>t \<Delta>N \<Delta>d = (v = (mat 1-(matrix_inv(J)**J\<^sub>h\<^sub>a\<^sub>t))*v u - matrix_inv(J)*v (\<Delta>N+\<Delta>d))"

(* \<delta> term definition Eq. 33*) (*assuming norm(v)\<le>\<epsilon>*)
definition "delta_def \<delta> (v::(real,3)vec) = (\<forall>t\<in>T.\<exists>\<epsilon>. \<epsilon>>0 \<and> norm(v)\<le>\<epsilon> \<longrightarrow> \<delta> \<ge> \<epsilon>/\<beta>\<^sub>m\<^sub>i\<^sub>n)"

(* \<gamma> term definition Eq. 31*)
definition "gamma_def \<gamma> B Q \<delta> E = (\<forall>t\<in>T. 
    if (norm (transpose (B) *v (Q*v E)) \<ge> \<sigma>) 
    then (\<gamma> = (\<delta>/norm(transpose (B) *v (Q*v E))) *s (transpose (B) *v (Q*v E))) 
    else (\<gamma> = (\<delta>/\<sigma>) *s (transpose (B) *v (Q*v E))))"

(* Attitude control law Eq. 12*)
definition "cont_law (\<tau> :: (real, 3) vec) u \<gamma> J\<^sub>h\<^sub>a\<^sub>t N\<^sub>h\<^sub>a\<^sub>t d\<^sub>h\<^sub>a\<^sub>t = (\<tau> = J\<^sub>h\<^sub>a\<^sub>t *v u + N\<^sub>h\<^sub>a\<^sub>t + d\<^sub>h\<^sub>a\<^sub>t + \<gamma>)"

(*################################################################################################*)

(* Call all the definitions that predefined with their constants and variables*)
definition "set_of_definitions \<phi> \<theta> \<psi> \<phi>\<^sub>d \<theta>\<^sub>d \<psi>\<^sub>d \<eta> \<eta>\<^sub>d \<eta>' \<eta>\<^sub>d' \<eta>'' \<eta>\<^sub>d'' u \<gamma> e e' e'' \<tau> d    
                               d\<^sub>h\<^sub>a\<^sub>t E v \<delta> C C\<^sub>h\<^sub>a\<^sub>t N N\<^sub>h\<^sub>a\<^sub>t \<Delta>N \<Delta>d A B W Q P K\<^sub>\<eta> K\<^sub>r J J\<^sub>h\<^sub>a\<^sub>t  
= (J_mat J \<phi> \<theta> \<psi> \<and> J\<^sub>h\<^sub>a\<^sub>t_mat J\<^sub>h\<^sub>a\<^sub>t \<phi> \<theta> \<psi>  \<and> K\<^sub>\<eta>_mat K\<^sub>\<eta> \<and> K\<^sub>r_mat K\<^sub>r \<and> W_mat W \<phi> \<theta> \<psi> \<and> A_mat A \<and> 
B_mat B \<and> P_mat P \<and> Q_mat Q \<and> torq_fun \<tau> \<and> C_mat C  \<phi> \<theta> \<psi> \<and> C\<^sub>h\<^sub>a\<^sub>t_mat C\<^sub>h\<^sub>a\<^sub>t \<phi> \<theta> \<psi>  \<and> Euler_vec \<eta> \<phi> \<theta> \<psi>
\<and> att_dyms \<tau> J C \<eta> \<phi> \<theta> \<psi> d \<and> error_vec e \<eta> \<eta>\<^sub>d \<phi> \<theta> \<psi> \<and> dot_error_vec e e' \<eta> \<eta>\<^sub>d \<eta>' \<eta>\<^sub>d' \<phi> \<theta> \<psi> \<and> 
N_vec N C \<eta> \<eta>' \<phi> \<theta> \<psi> \<and> N\<^sub>h\<^sub>a\<^sub>t_vec N\<^sub>h\<^sub>a\<^sub>t C\<^sub>h\<^sub>a\<^sub>t \<eta> \<phi> \<theta> \<psi> \<and> E_vec (E::(real,6)vec)\<eta> \<eta>' \<and> ddot_\<eta>_vec \<eta>\<^sub>d \<eta>\<^sub>d' \<eta>\<^sub>d'' \<phi>\<^sub>d \<theta>\<^sub>d \<psi>\<^sub>d     
 \<and> ddot_error_vec e e' e'' \<eta> \<eta>' \<eta>'' \<eta>\<^sub>d \<eta>\<^sub>d' \<eta>\<^sub>d'' \<phi> \<theta> \<psi> \<phi>\<^sub>d \<theta>\<^sub>d \<psi>\<^sub>d \<and> v_eq v u J J\<^sub>h\<^sub>a\<^sub>t \<Delta>N \<Delta>d \<and>
 cont_u u \<eta>\<^sub>d'' K\<^sub>r K\<^sub>\<eta> e e' \<and> delta_def \<delta> v \<and> gamma_def \<gamma> B Q \<delta> E \<and> cont_law \<tau> u \<gamma> J\<^sub>h\<^sub>a\<^sub>t N\<^sub>h\<^sub>a\<^sub>t d\<^sub>h\<^sub>a\<^sub>t)"

lemma matrix_unity: 
  fixes J :: "real^3^3"
    and x :: "real^3" 
assumes "invertible J"
  shows "matrix_inv(J) *v (J *v x) = x" 
proof-
    have x1: "matrix_inv(J) *v (J *v x) = (matrix_inv(J) ** J) *v x " 
      by (simp add: matrix_vector_mul_assoc)
    have "J ** matrix_inv(J) = mat 1"  
      by (smt assms matrix_inv_def invertible_def matrix_matrix_mult_def someI2)   
    from this x1 have "(matrix_inv(J) ** J) *v x =  x" 
      using matrix_left_right_inverse matrix_vector_mul_lid by force
    thus ?thesis 
      using x1 by auto
qed

lemma matrix_diff_vect_distrib: "(A - B) *v x = A *v x - B *v (x :: 'a :: ring_1 ^ 'n)"
  unfolding matrix_vector_mult_def
  by vector (simp add: sum_subtractf left_diff_distrib)

lemma matrix_add_vect_distrib: "(A + B) *v x = A *v x + B *v x"
  unfolding matrix_vector_mult_def
  by vector (simp add: sum.distrib distrib_right)

lemma matrix_vector_right_distrib: "M *v (x + w) = M *v x + M *v w"
  unfolding matrix_vector_mult_def
  by vector (simp add: sum.distrib distrib_left)

lemma matrix_vector_right_distrib_diff: "(M :: 'a :: ring_1 ^ 'nr ^ 'nc) *v (y - w) = M *v y - M *v w"
  unfolding matrix_vector_mult_def
  by vector (simp add: sum_subtractf right_diff_distrib)

theorem Eq_19:
  assumes "assump1 (d ::(real,3)vec) d\<^sub>h\<^sub>a\<^sub>t \<Delta>d" and "assump2 \<Delta>N N  N\<^sub>h\<^sub>a\<^sub>t" and "\<forall>t. t\<in>T"
      and "att_dyms \<tau> J C \<eta> \<phi> \<theta> \<psi> d" and "cont_law \<tau> u \<gamma> J\<^sub>h\<^sub>a\<^sub>t N\<^sub>h\<^sub>a\<^sub>t d\<^sub>h\<^sub>a\<^sub>t" 
      and "J_mat J \<phi> \<theta> \<psi>" and "J\<^sub>h\<^sub>a\<^sub>t_mat J\<^sub>h\<^sub>a\<^sub>t \<phi> \<theta> \<psi>" and "v_eq v u J J\<^sub>h\<^sub>a\<^sub>t \<Delta>N \<Delta>d" 
      and "set_of_definitions \<phi> \<theta> \<psi> \<phi>\<^sub>d \<theta>\<^sub>d \<psi>\<^sub>d \<eta> \<eta>\<^sub>d \<eta>' \<eta>\<^sub>d' \<eta>'' \<eta>\<^sub>d'' u \<gamma> e e' e'' \<tau> d    
                               d\<^sub>h\<^sub>a\<^sub>t E v \<delta> C C\<^sub>h\<^sub>a\<^sub>t N N\<^sub>h\<^sub>a\<^sub>t \<Delta>N \<Delta>d A B W Q P K\<^sub>\<eta> K\<^sub>r J J\<^sub>h\<^sub>a\<^sub>t"
    shows "\<eta>'' = u - v + matrix_inv(J)*v \<gamma>" 
proof-
  have "\<tau> = J *v \<eta>'' + C *v \<eta>' + d"  
    using assms att_dyms_def by simp
  then have " J *v \<eta>'' + C *v \<eta>' + d = J\<^sub>h\<^sub>a\<^sub>t *v u + N\<^sub>h\<^sub>a\<^sub>t + d\<^sub>h\<^sub>a\<^sub>t + \<gamma>" 
    unfolding cont_law_def using assms cont_law_def by blast
  then have " J *v \<eta>'' + N + d = J\<^sub>h\<^sub>a\<^sub>t *v u + N\<^sub>h\<^sub>a\<^sub>t + d\<^sub>h\<^sub>a\<^sub>t + \<gamma>" 
    using N_vec_def assms(9) set_of_definitions_def by auto
  then have x1:" J *v \<eta>'' = J\<^sub>h\<^sub>a\<^sub>t *v u + N\<^sub>h\<^sub>a\<^sub>t - N + d\<^sub>h\<^sub>a\<^sub>t - d + \<gamma>" 
    by (simp add: add_implies_diff diff_add_eq semiring_normalization_rules(23))
  have "\<Delta>N = N\<^sub>h\<^sub>a\<^sub>t-N"
    by (smt B_mat_def assms(9) exhaust_3 set_of_definitions_def) 
    from this x1  have "J *v \<eta>'' = J\<^sub>h\<^sub>a\<^sub>t *v u + \<gamma> + \<Delta>N +  \<Delta>d"
    using assms(1) assump1_def by auto
  then have "\<eta>'' = matrix_inv(J) *v (J\<^sub>h\<^sub>a\<^sub>t *v u + \<gamma> + \<Delta>N + \<Delta>d)" 
    using assms matrix_unity J_mat_def by (metis (no_types, lifting))
  then have "\<eta>'' = (matrix_inv(J) ** J\<^sub>h\<^sub>a\<^sub>t) *v u + matrix_inv(J) *v \<gamma> +  matrix_inv(J) *v (\<Delta>N + \<Delta>d)" 
    by (metis (no_types, lifting) diff_diff_eq2 diff_minus_eq_add matrix_vector_mul_assoc
        matrix_vector_right_distrib_diff minus_diff_eq)    
  then have "\<eta>'' = u + ((matrix_inv(J) ** J\<^sub>h\<^sub>a\<^sub>t)- mat 1)*v u + matrix_inv(J) *v \<gamma> + matrix_inv(J) *v (\<Delta>N + \<Delta>d)"
    by (simp add: matrix_diff_vect_distrib add_diff_eq)
  then have x1:"\<eta>'' = u - ((mat 1-(matrix_inv(J)**J\<^sub>h\<^sub>a\<^sub>t))*v u - matrix_inv(J)*v (\<Delta>N+\<Delta>d)) + matrix_inv(J) *v \<gamma>"
    by (simp add: diff_add_eq matrix_diff_vect_distrib)
   have x2:"v = (mat 1-(matrix_inv(J)**J\<^sub>h\<^sub>a\<^sub>t))*v u - matrix_inv(J)*v (\<Delta>N+\<Delta>d)"
    using assms v_eq_def by fast
  from x1 x2 show ?thesis 
    by simp
qed

lemma Eq_22:
  assumes "set_of_definitions \<phi> \<theta> \<psi> \<phi>\<^sub>d \<theta>\<^sub>d \<psi>\<^sub>d \<eta> \<eta>\<^sub>d \<eta>' \<eta>\<^sub>d' \<eta>'' \<eta>\<^sub>d'' u \<gamma> e e' e'' \<tau> d    
                               d\<^sub>h\<^sub>a\<^sub>t E v \<delta> C C\<^sub>h\<^sub>a\<^sub>t N N\<^sub>h\<^sub>a\<^sub>t \<Delta>N \<Delta>d A B W Q P K\<^sub>\<eta> K\<^sub>r J J\<^sub>h\<^sub>a\<^sub>t"    
    shows "E' = A *v E + B *v (v - (matrix_inv(J) *v \<gamma>))"
proof -
  have "e'' = \<eta>\<^sub>d''- \<eta>''" 
    using assms ddot_error_vec_def set_of_definitions_def by metis
  thus ?thesis 
    by (smt B_mat_def assms exhaust_3 set_of_definitions_def)
qed

(**************************************************************************************************)
section \<open>STABILITY ANALYSIS\<close>
(**************************************************************************************************)
(**************************************************************************************************)
text \<open>Lyapunov function\<close>
(**************************************************************************************************)
(* Lyapunov function definition *)
definition "Lyapunov V E = (\<forall>t\<in>T.  if (E :: (real,6) vec) \<noteq>0   
                     then (\<exists>a. V(E)= (a:: real) \<and> continuous_on D6_vec_set V  \<and> V(E)>0) else V(E) = 0)"
                                 
lemma test_lyp0:
  assumes "\<forall>t. t\<in>T" "E\<in>D6_vec_set"  "E=0" "Lyapunov V E"
    shows "V(E) = 0" using assms Lyapunov_def  by force

lemma test_lyp1:
  assumes "\<forall>t. t\<in>T" "E\<in>D6_vec_set"  "E\<noteq>0" "Lyapunov V E" 
    shows "V(E) >0" using assms Lyapunov_def    by metis
(* Eq. 27 *)
lemma Lyp_fun:
  assumes "pos_def_symmetric_matrix Q" "\<forall>E. E\<noteq>0" 
  shows "\<exists>Q. (E \<bullet> (Q *v E))>0" 
    using assms pos_def_symmetric_matrix_def pos_def_6x6_matrix_def by blast

lemma vec_op:
  fixes A Q :: "real^6^6"
    and E:: "real^6"
  shows "(A *v E) \<bullet> (Q *v E) = E \<bullet> ((transpose(A) ** Q) *v E)"
    by (metis dot_matrix_product dot_matrix_vector_mul dot_rowvector_columnvector)

(* Lyapunov matrix A\<^sup>T*Q + Q*A = -P *)
lemma Lya_mat: 
  fixes A :: "((real, 6) vec, 6) vec" 
  assumes "pos_def_symmetric_matrix Q" and "pos_def_symmetric_matrix P" 
      and "A_mat A" and "P_mat P" and "Q_mat Q"
      and "det(A - (mat egn)) =0" and "egn<0" "\<forall>r. r \<noteq> 0"
    shows "\<exists>!Q. transpose (A) ** Q +  Q ** A = -P"  
      using assms pos_def_symmetric_matrix_def pos_def_6x6_matrix_def by blast

(**************************************************************************************************)
text \<open>Stability proof\<close>
(**************************************************************************************************)
(* Eqs. 28-30 *)
theorem Stb_Eqs_28_30: 
 assumes "\<forall>E. E\<noteq>0"and"Lyapunov V E"and"V(E) = E \<bullet> (Q *v E)" 
     and "A_mat A"and"E' = A *v E + B *v (v - (matrix_inv(J) *v \<gamma>))"
     and "(\<forall>t\<in>T. ((\<lambda>t. V(E)) has_derivative (\<lambda>t. V'(E))) (at t within T))"
   shows "V'(E) = - (E \<bullet> (P *v E)) + 2 * (((E v* Q) v* B) \<bullet> (v - matrix_inv(J) *v \<gamma>))"
proof -
   have "V'(E) = E' \<bullet> (Q *v E) + E \<bullet> (Q *v E')" 
     using assms add_cancel_left_left rel_simps(93) by blast 
   then have "V'(E) = E \<bullet> ((transpose (A) ** Q + Q ** A)*v E) + 2*(((E v* Q) v* B) \<bullet> (v - matrix_inv(J) *v \<gamma>))"
     using assms Eq_22 vec_op  rel_simps(93) by simp
   then have "V'(E) = - (E \<bullet> (P *v E)) + 2 * (((E v* Q) v* B) \<bullet> (v - matrix_inv(J) *v \<gamma>))" 
     using assms by blast
   then show ?thesis 
     by blast
qed
(* Eq. 32 *)
theorem Eq_32:
  assumes "\<forall>t. t\<in>T" and "assump3_b J J\<^sub>h\<^sub>a\<^sub>t \<phi> \<theta> \<psi>" and"norm(transpose(B)*v(Q*v E)) \<ge> \<sigma>"and"delta_def \<delta> v"  
      and "\<exists>E. E\<noteq>0" and "set_of_definitions \<phi> \<theta> \<psi> \<phi>\<^sub>d \<theta>\<^sub>d \<psi>\<^sub>d \<eta> \<eta>\<^sub>d \<eta>' \<eta>\<^sub>d' \<eta>'' \<eta>\<^sub>d'' u \<gamma> e e' e'' \<tau> d    
                               d\<^sub>h\<^sub>a\<^sub>t E v \<delta> C C\<^sub>h\<^sub>a\<^sub>t N N\<^sub>h\<^sub>a\<^sub>t \<Delta>N \<Delta>d A B W Q P K\<^sub>\<eta> K\<^sub>r J J\<^sub>h\<^sub>a\<^sub>t" 
    shows "(((E v* Q) v* B) \<bullet> (v - matrix_inv(J) *v \<gamma>)) \<le> norm (transpose (B) *v (Q*v E))* (norm(v) - (\<beta>\<^sub>m\<^sub>i\<^sub>n * \<delta>)) "
proof - 
  have x1:"((E v* Q) v* B) \<bullet>  (v - matrix_inv(J) *v \<gamma>) = (((E v* Q) v* B) \<bullet>  v) - (((E v* Q) v* B) \<bullet> (matrix_inv(J) *v \<gamma>)) "
    by (simp add: inner_diff_right)     
  then have x2:" norm((((E v* Q) v* B) \<bullet> v) - (((E v* Q) v* B) \<bullet> (matrix_inv(J) *v \<gamma>))) \<le> 
              norm (((E v* Q) v* B) \<bullet> v) + norm(((E v* Q) v* B) \<bullet> (matrix_inv(J) *v \<gamma>)) "
    using norm_triangle_ineq4 by blast
  have x3:"norm (((E v* Q) v* B) \<bullet> v) \<le> norm ((E v* Q) v* B) * norm(v) " 
     by (simp add: Cauchy_Schwarz_ineq2)
   have x4:"norm(((E v* Q) v* B) \<bullet> (matrix_inv(J) *v \<gamma>)) \<le> norm((E v* Q) v* B) * norm(matrix_inv(J) *v \<gamma>)"
     by (simp add: Cauchy_Schwarz_ineq2)
   from x1 x2 x3 x4 have x5:"((E v* Q) v* B) \<bullet>  (v - matrix_inv(J) *v \<gamma>) \<le> 
      norm((E v* Q) v* B) * norm(v) - ((E v* Q) v* B) \<bullet> (matrix_inv(J) *v \<gamma>)" 
     by fastforce
   have x6:"norm((E v* Q) v* B) = norm(transpose(B) *v (Q*v E)) "
    by (smt B_mat_def assms exhaust_3 set_of_definitions_def)
  from x5 x6 have "((E v* Q) v* B) \<bullet>  (v - matrix_inv(J) *v \<gamma>) \<le> 
      norm(transpose(B) *v (Q*v E)) * norm(v) - (transpose(B) *v (Q*v E)) \<bullet> ((matrix_inv(J)) *v \<gamma>)"
    by (meson Eq_22 add_cancel_left_left assms rel_simps(93))
  then have "((E v* Q) v* B) \<bullet>  (v - matrix_inv(J) *v \<gamma>) \<le> 
      norm(transpose(B) *v (Q *v E)) * norm(v) - (transpose(B) *v (Q*v E)) \<bullet> ( norm(matrix_inv(J)) *s \<gamma>)"
    by (meson Eq_22 add_cancel_left_left assms(5) assms(6) rel_simps(93))
  then have "((E v* Q) v* B) \<bullet>  (v - matrix_inv(J) *v \<gamma>) \<le> 
      norm(transpose(B) *v (Q*v E)) * norm(v) - norm(matrix_inv(J)) *((transpose(B) *v (Q*v E)) \<bullet> \<gamma>)"
    by(simp add:  scalar_mult_eq_scaleR)  
  then have "((E v* Q) v* B) \<bullet>  (v - matrix_inv(J) *v \<gamma>) \<le>
      norm(transpose(B) *v (Q *v E)) * norm(v) - \<beta>\<^sub>m\<^sub>i\<^sub>n *((transpose(B) *v (Q*v E)) \<bullet> \<gamma>)"
    using  set_of_definitions_def assump2_def by (smt B_mat_def assms(6) exhaust_3)
  then have "((E v* Q) v* B) \<bullet>  (v - matrix_inv(J) *v \<gamma>) \<le>
      norm(transpose(B) *v (Q*v E)) * norm(v) - \<beta>\<^sub>m\<^sub>i\<^sub>n * norm(transpose(B) *v (Q*v E)) * norm(\<gamma>)"
    using  set_of_definitions_def assump2_def by (smt B_mat_def assms(6) exhaust_3)
  then have "((E v* Q) v* B) \<bullet>  (v - matrix_inv(J) *v \<gamma>) \<le>
      norm(transpose(B) *v (Q*v E)) *(norm(v) - \<beta>\<^sub>m\<^sub>i\<^sub>n *  norm(\<gamma>))"
    by (smt inner_diff_right inner_real_def mult.assoc mult.left_commute)
  then have "((E v* Q) v* B) \<bullet>  (v - matrix_inv(J) *v \<gamma>) \<le>
      norm(transpose(B) *v (Q*v E)) *(norm(v) - \<beta>\<^sub>m\<^sub>i\<^sub>n * \<delta>)"
    by (smt B_mat_def assms(6) exhaust_3 rel_simps(93) set_of_definitions_def)
  thus ?thesis 
    by blast
qed

(* Eq. 34 *)
theorem Eq_34:
  assumes "set_of_definitions \<phi> \<theta> \<psi> \<phi>\<^sub>d \<theta>\<^sub>d \<psi>\<^sub>d \<eta> \<eta>\<^sub>d \<eta>' \<eta>\<^sub>d' \<eta>'' \<eta>\<^sub>d'' u \<gamma> e e' e'' \<tau> d    
                               d\<^sub>h\<^sub>a\<^sub>t E v \<delta> C C\<^sub>h\<^sub>a\<^sub>t N N\<^sub>h\<^sub>a\<^sub>t \<Delta>N \<Delta>d A B W Q P K\<^sub>\<eta> K\<^sub>r J J\<^sub>h\<^sub>a\<^sub>t" 
      and "assump1 d d\<^sub>h\<^sub>a\<^sub>t \<Delta>d" and "assump2 \<Delta>N N  N\<^sub>h\<^sub>a\<^sub>t" and "assump3_a \<eta>\<^sub>d''" and "assump3_b J J\<^sub>h\<^sub>a\<^sub>t \<phi> \<theta> \<psi>"
    shows "norm (v) \<le> (\<xi> * (H + (norm(K\<^sub>r)*norm(e'))+ (norm(K\<^sub>\<eta>)*norm(e))) + (\<beta>\<^sub>m\<^sub>a\<^sub>x*(S + D)))" 
proof-
  have "v = (mat 1-(matrix_inv(J)**J\<^sub>h\<^sub>a\<^sub>t))*v u - matrix_inv(J)*v (\<Delta>N+\<Delta>d)" 
    using assms v_eq_def set_of_definitions_def by fast
  then have "norm(v) \<le> norm((mat 1-(matrix_inv(J)**J\<^sub>h\<^sub>a\<^sub>t))*v u - matrix_inv(J)*v (\<Delta>N+\<Delta>d))"
    by fastforce
  then have "norm(v) \<le>norm((mat 1-(matrix_inv(J)**J\<^sub>h\<^sub>a\<^sub>t))*v u) + norm((matrix_inv(J)) *v (\<Delta>N+\<Delta>d))"
    using norm_triangle_ineq4 order_trans by blast
  then have "norm(v) \<le> (norm(mat 1-(matrix_inv(J)**J\<^sub>h\<^sub>a\<^sub>t)) * norm(u)) + (norm(matrix_inv(J)) * (norm(\<Delta>N) + norm(\<Delta>d)))"
     by (smt B_mat_def assms(1) exhaust_3 set_of_definitions_def)
  then have "norm(v) \<le> norm(mat 1-(matrix_inv(J)**J\<^sub>h\<^sub>a\<^sub>t)) * norm(\<eta>\<^sub>d'' + K\<^sub>r *v e' + K\<^sub>\<eta> *v e) 
                     + norm (matrix_inv(J))* (norm(\<Delta>N)+ norm(\<Delta>d))"  
    using assms cont_u_def set_of_definitions_def by metis
  then have "norm(v) \<le> norm(mat 1-(matrix_inv(J)**J\<^sub>h\<^sub>a\<^sub>t)) * (norm(\<eta>\<^sub>d'') + (norm(K\<^sub>r) * norm(e')) + (norm(K\<^sub>\<eta>) * norm(e)))
                     + norm (matrix_inv(J))* (norm(\<Delta>N)+ norm(\<Delta>d))"
    using assms norm_add_rule_thm B_mat_def exhaust_3 set_of_definitions_def by smt  
  then have "norm(v) \<le> \<xi> * (H + (norm(K\<^sub>r) * norm(e')) + (norm(K\<^sub>\<eta>) * norm(e)))
                     + \<beta>\<^sub>m\<^sub>a\<^sub>x * (S+D)"   
    by (meson assms assump1_def assump2_def assump3_a_def mult_nonneg_nonneg norm_ge_zero mult_right_mono mult_mono 
          mult_nonneg_nonneg mult_right_mono norm_ge_zero less_irrefl Eq_22 add_cancel_left_right rel_simps(93))
  thus ?thesis 
    by blast
qed

(* Eq. 35 *)
theorem Eq_35:
  assumes "\<forall>t. t\<in>T""delta_def \<delta> v"
      and "norm (v) \<le> (\<xi> * (H + (norm(K\<^sub>r)*norm(e'))+ (norm(K\<^sub>\<eta>)*norm(e))) + (\<beta>\<^sub>m\<^sub>a\<^sub>x*(S + D)))" (*from Eq_34*)
    shows "\<exists>\<delta>. \<delta> \<ge> (\<xi>/\<beta>\<^sub>m\<^sub>i\<^sub>n) * (H + (norm(K\<^sub>r)*norm(e'))+ (norm(K\<^sub>\<eta>)*norm(e))) + (\<beta>\<^sub>m\<^sub>a\<^sub>x/\<beta>\<^sub>m\<^sub>i\<^sub>n)*(S + D)"
proof-
  fix x y:: "real^3"
  have x1:"\<beta>\<^sub>m\<^sub>a\<^sub>x>0 \<and> \<beta>\<^sub>m\<^sub>i\<^sub>n>0 \<and> S>0 \<and> D>0 \<and> \<xi>>0 \<and> H>0 \<and> norm x\<ge>0" 
    using \<beta>\<^sub>m\<^sub>a\<^sub>x_def \<beta>\<^sub>m\<^sub>i\<^sub>n_def S_def D_def \<xi>_def H_def by force
  have x2:"y>0 \<Longrightarrow> 0+y>0"  by simp
  from x1 x2 have x3:"(\<xi> * (H + (norm(K\<^sub>r)*norm(e'))+ (norm(K\<^sub>\<eta>)*norm(e))) + (\<beta>\<^sub>m\<^sub>a\<^sub>x*(S + D))) > 0" 
    by (smt distrib_left mult.commute mult_nonneg_nonneg norm_ge_zero real_mult_le_cancel_iff1)
  then have "\<exists>\<delta>. \<delta> \<ge> (\<xi> * (H + (norm(K\<^sub>r)*norm(e'))+ (norm(K\<^sub>\<eta>)*norm(e))) + (\<beta>\<^sub>m\<^sub>a\<^sub>x*(S + D)))/\<beta>\<^sub>m\<^sub>i\<^sub>n" 
    using assms \<beta>\<^sub>m\<^sub>i\<^sub>n_def delta_def_def  divide_pos_pos divide_strict_right_mono by blast
  then have "\<exists>\<delta>. \<delta> \<ge> (\<xi>/\<beta>\<^sub>m\<^sub>i\<^sub>n) * (H + (norm(K\<^sub>r)*norm(e'))+ (norm(K\<^sub>\<eta>)*norm(e))) + (\<beta>\<^sub>m\<^sub>a\<^sub>x*(S + D))/\<beta>\<^sub>m\<^sub>i\<^sub>n"
    by argo
  thus ?thesis 
    by auto
qed

(* Eqs 36 and 37 *)
theorem Stb_Eq_36_37:
assumes "set_of_definitions \<phi> \<theta> \<psi> \<phi>\<^sub>d \<theta>\<^sub>d \<psi>\<^sub>d \<eta> \<eta>\<^sub>d \<eta>' \<eta>\<^sub>d' \<eta>'' \<eta>\<^sub>d'' u \<gamma> e e' e'' \<tau> d    
                            d\<^sub>h\<^sub>a\<^sub>t E v \<delta> C C\<^sub>h\<^sub>a\<^sub>t N N\<^sub>h\<^sub>a\<^sub>t \<Delta>N \<Delta>d A B W Q P K\<^sub>\<eta> K\<^sub>r J J\<^sub>h\<^sub>a\<^sub>t" 
    and "assump1 d d\<^sub>h\<^sub>a\<^sub>t \<Delta>d" and "assump3_a \<eta>\<^sub>d''" and "assump3_b J J\<^sub>h\<^sub>a\<^sub>t \<phi> \<theta> \<psi>"
    and "\<forall>E. E\<noteq>0" and "Lyapunov V E" and "V(E) = E \<bullet> (Q *v E)"
    and "(\<forall>t\<in>T. ((\<lambda>t. V(E)) has_derivative (\<lambda>t. V'(E))) (at t within T))"
    and "\<eta>'' = u - v + matrix_inv(J)*v \<gamma>" (* from Eq_19 *)
    and "E' = A *v E + B *v (v - (matrix_inv(J) *v \<gamma>))" (* from Eq_22 *)
    and "V'(E) = - (E \<bullet> (P *v E)) + 2 * (E \<bullet> (Q *v (B *v (v - matrix_inv (J) *v \<gamma>))))" (* from Eq_30 *)
  shows "norm (transpose (B) *v (Q*v E)) \<ge> \<sigma> \<Longrightarrow> V'(E) < 0" 
    and "norm (transpose (B) *v (Q*v E)) < \<sigma> \<Longrightarrow> V'(E) < 0"
    and "((\<lambda>t. norm(E)) \<longlongrightarrow> 0) (at t within T)"
proof- 
   show "norm (transpose (B) *v (Q*v E)) \<ge> \<sigma> \<Longrightarrow> V'(E) < 0"
    using assms Eq_22 rel_simps(93) by metis
  then show "norm (transpose (B) *v (Q*v E)) < \<sigma> \<Longrightarrow> V'(E) < 0"
    using assms Eq_22 rel_simps(93) by metis
  show "((\<lambda>t. norm(E)) \<longlongrightarrow> 0) (at t within T)" 
    using assms by auto
qed  

end