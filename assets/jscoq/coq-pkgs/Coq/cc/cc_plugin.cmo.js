function(fe){"use strict";var
al=104,aC=".",bV=108,bW="$l",bM="  [",bK=3901498,bL=" : ",bU=-431191102,bR="$n",aY=-912009552,U=250,$="Init",aB=124,bJ=127,N=246,aD="congruence",bQ="[",bI="A",bT="with",aF="]",bH=915186972,bP=888453194,_="Logic",bO=" and ",bN=109,bG=-318868643,aE=107,bS="Heq",aW="f_equal",aA=15500,aX=1e3,x=fe.jsoo_runtime,r=x.caml_check_bound,aj=x.caml_int_compare,ay=x.caml_make_vect,d=x.caml_new_string,T=x.caml_obj_tag,ak=x.caml_register_global,s=x.caml_wrap_exception;function
a(a,b){return a.length==1?a(b):x.caml_call_gen(a,[b])}function
b(a,b,c){return a.length==2?a(b,c):x.caml_call_gen(a,[b,c])}function
j(a,b,c,d){return a.length==3?a(b,c,d):x.caml_call_gen(a,[b,c,d])}function
z(a,b,c,d,e){return a.length==4?a(b,c,d,e):x.caml_call_gen(a,[b,c,d,e])}function
bF(a,b,c,d,e,f){return a.length==5?a(b,c,d,e,f):x.caml_call_gen(a,[b,c,d,e,f])}function
az(a,b,c,d,e,f,g,h){return a.length==7?a(b,c,d,e,f,g,h):x.caml_call_gen(a,[b,c,d,e,f,g,h])}function
fd(a,b,c,d,e,f,g,h,i,j){return a.length==9?a(b,c,d,e,f,g,h,i,j):x.caml_call_gen(a,[b,c,d,e,f,g,h,i,j])}var
h=x.caml_get_global_data(),au=d("cc_plugin"),o=h.Constr,l=h.Names,aa=h.Hashset,a0=h.Sorts,i=h.Util,t=h.Not_found,a7=h.Term,e=h.EConstr,P=h.Typing,g=h.Int,v=h.Queue,c=h.Pp,aO=h.Control,E=h.CErrors,bc=h.Environ,ba=h.Assert_failure,C=h.Termops,p=h.Tacmach,aH=h.Feedback,ad=h.Hashtbl,af=h.Pervasives,S=h.CamlinternalLazy,q=h.Tacticals,k=h.Proofview,F=h.Tactics,bx=h.Evarsolve,bA=h.DAst,aT=h.Coqlib,bv=h.Equality,bu=h.Context,bq=h.CClosure,br=h.Reductionops,av=h.Stdarg,aw=h.Genarg,ax=h.Loc,bD=h.Ltac_plugin,aG=[0,0],dr=d("Out of depth ... "),dq=d("Out of instances ... "),ds=d("First run was incomplete, completing ... "),dp=d("Executing ... "),dn=d("Running E-matching algorithm ... "),dm=d("paf_of_patt: pattern is trivial"),dj=d("wrong incomplete class."),dc=d(" ... "),dd=d(" = "),de=d("Checking if "),db=d("Yes"),df=d("No"),c_=d(aC),c$=d("Processing mark for term "),c7=d("weird error in injection subterms merge."),c8=[0,d("add_pacs")],c5=d(aC),c6=d("Updating term "),c2=d(aC),c3=d(bO),c4=d("Merging "),cY=d(aC),cZ=d(bO),c0=d("Linking "),cX=[0,d("plugins/cc/ccalgo.ml"),637,2],cQ=d(aF),cR=d(" <> "),cS=d(bL),cT=d(bM),cU=d("Adding new disequality, depth="),cL=d(aF),cM=d(" == "),cN=d(bL),cO=d(bM),cP=d("Adding new equality, depth="),cK=d("discarding redundant (dis)equality"),cG=d(aF),cH=d(bQ),cD=d(aF),cE=d(":="),cF=d(bQ),cC=d("incomplete matching."),cs=d("not a node."),ct=[0,d("subterms")],cj=d("not a constructor."),ck=[0,d("get_constructor")],cf=d("not a representative."),cg=[0,d("get_representative")],b7=d("signature already entered."),b8=[0,d("enter")],bY=[0,d("Congruence"),[0,d("Verbose"),0]],bZ=d("Congruence Verbose"),cp=d("Ccalgo.Discriminable"),cv=d(bI),cx=d(bI),dg=d("_eps_"),dt=d("invalid cc transitivity."),du=d("not enough args."),dv=[0,d("nth_arg")],dw=[0,1,20],dx=d("equal_proof "),dy=[0,1,20],dz=d("edge_proof "),dA=[0,1,20],dB=d("constr_proof "),dD=d(","),dC=d("}"),dE=d("{"),dF=[0,1,20],dG=d("path_proof "),dH=[0,1,20],dI=d("congr_proof "),dJ=[0,1,20],dK=d("ind_proof "),d8=[0,d("plugins/cc/cctac.ml"),254,9],ec=d("f"),ed=d("I don't know how to handle dependent equality"),eE=[0,0],ev=d("("),ew=d(")"),ep=[0,1],en=d("Goal solved, generating proof ..."),em=d("Computation completed."),el=d("Problem built, solving ..."),ek=d("Reading subgoal ..."),eo=[13,0,0,0],es=d("Goal is solvable by congruence but some arguments are missing."),et=d("  replacing metavariables by arbitrary terms."),eu=d(')",'),ex=d('"congruence with ('),ey=d("  Try "),ez=d("Incomplete"),eA=d("congruence failed"),ej=d(bS),ei=d("H"),eg=d("e"),eh=d("X"),ee=d(bS),d$=[0,0],ea=[0,1],d7=d("t"),dL=d("CC"),dM=d(aW),dN=[0,d($),[0,d(_),0]],dO=d("eq_rect"),dP=[0,d($),[0,d(_),0]],dR=d("eq_refl"),dS=[0,d($),[0,d(_),0]],dT=d("eq_sym"),dU=[0,d($),[0,d(_),0]],dW=d("eq_trans"),dX=[0,d($),[0,d(_),0]],dY=d("eq"),dZ=[0,d($),[0,d(_),0]],d0=d("False"),d1=[0,d($),[0,d(_),0]],eB=d("congruence failed."),eL=d(bW),eO=d(bT),eQ=d(bR),eT=d(aD),eW=d(bW),eZ=d(bT),e0=d(aD),e3=d(bR),e6=d(aD),e8=[0,d(aD),0],e_=d("cc"),fa=[0,d(aW),0],fc=d(aW),dk=h.Vars,di=h.Namegen,b1=h.Goptions,d2=h.Global,d3=h.Inductiveops,d4=h.Retyping,d9=h.Evarutil,eG=h.Pretype_errors,eH=h.Type_errors,eq=h.Detyping,er=h.Printer,eb=h.Evd,d_=h.Refine,eI=h.Mltop,V=5;function
A(d){var
c=aG[1];if(c){var
e=a(d,0);return b(aH[10],0,e)}return c}function
bX(a){aG[1]=a;return 0}var
b0=[0,0,bZ,bY,function(a){return aG[1]},bX];b(b1[4],0,b0);var
b2=g[1],b3=[0,function(b,a){return b===a?1:0},b2],am=a(ad[19],b3);function
b4(b,a){var
c=b[1]===a[1]?1:0,d=a[2],e=b[2],f=c?e===d?1:0:c;return f}var
b5=[0,b4,function(c){var
d=c[1],e=a(g[1],c[2]),f=a(g[1],d);return b(aa[2][1],f,e)}],ae=a(ad[19],b5);function
b6(f,e,d){if(b(ae[11],d[1],e)){var
g=a(c[3],b7);j(E[3],0,b8,g)}else
j(ae[10],d[1],e,f);return j(am[10],d[2],f,e)}function
b9(c,a){return b(ae[7],a[1],c)}function
b_(a,c){try{var
d=b(am[7],a[2],c);b(ae[6],a[1],d);var
e=b(am[6],a[2],c);return e}catch(a){a=s(a);if(a===t)return 0;throw a}}function
b$(c,a){function
d(a){return b_(c,a)}return b(g[2][13],d,a)}var
ca=[0,function(b,a){var
c=aj(b[1],a[1]),e=a[3],f=a[2],g=b[3],h=b[2];if(0===c){var
d=aj(h,f);return 0===d?j(i[17][51],aj,g,e):d}return c}],cb=[0,function(b,a){var
c=aj(b[1],a[1]),d=a[2],e=b[2];return 0===c?aj(e,d):c}],n=a(i[21][1],ca),m=a(i[21][1],cb);function
aZ(b,a){var
c=0===b[0]?0===b[1]?0===a[0]?0===a[1]?1:0:0:0===a[0]?0===a[1]?0:1:0:0===a[0]?0:1;return c?1:0}function
aI(m,k){var
c=m,a=k;for(;;){switch(c[0]){case
0:if(0===a[0])return b(o[79],c[1],a[1]);break;case
1:if(1===a[0]){var
n=a[2],p=c[2],f=aZ(c[1],a[1]);return f?aZ(p,n):f}break;case
2:if(2===a[0])return b(l[1][1],c[1],a[1]);break;case
3:if(3===a[0]){var
q=a[2],r=c[2],g=aI(c[1],a[1]);if(g){var
c=r,a=q;continue}return g}break;default:if(4===a[0]){var
d=a[1],e=c[1],h=e[2]===d[2]?1:0,s=d[3],t=d[1][1],u=e[3],v=e[1][1];if(h){var
i=u===s?1:0;if(i)return b(l[46],v,t);var
j=i}else
var
j=h;return j}}return 0}}function
aJ(c){switch(c[0]){case
0:var
e=a(o[93],c[1]);return b(aa[2][1],1,e);case
1:var
f=c[1],g=a(a0[6],c[2]),h=a(a0[6],f);return j(aa[2][3],2,h,g);case
2:var
i=a(l[1][3],c[1]);return b(aa[2][1],3,i);case
3:var
k=c[1],m=aJ(c[2]),n=aJ(k);return j(aa[2][3],4,n,m);default:var
d=c[1],p=d[3],q=d[2],r=a(l[50],d[1][1]);return z(aa[2][4],5,r,q,p)}}var
G=a(ad[19],[0,o[79],o[93]]),W=a(ad[19],[0,aI,aJ]),aK=a(ad[19],[0,l[1][1],l[1][3]]),cc=[0,a(o[1],af[8])],a1=[0,[1,af[8],[0,af[8],af[8],0]],af[8],n[1],0,cc];function
a2(c){var
b=a(W[1],V);return[0,V,0,ay(5,a1),a(G[1],V),0,b]}function
cd(e,b){var
f=a(p[2],b),h=a(p[8],b),i=a(G[1],V),j=a(aK[1],V),k=g[2][1],l=a(v[2],0),m=a(v[2],0),n=g[2][1],c=a(am[1],V),d=[0,a(ae[1],V),c];return[0,a2(0),d,n,m,l,0,0,k,j,e,0,i,h,f]}function
ce(a){return a[1]}function
y(e,g){var
c=0,a=g;for(;;){var
d=r(e[3],a)[a+1][2];if(0<=d){var
c=[0,a,c],a=d;continue}var
f=function(b){r(e[3],b)[b+1][2]=a;return 0};b(i[17][14],f,c);return a}}function
K(e,b){var
d=r(e[3],b)[b+1][1];if(0===d[0])return d[1];var
f=a(c[3],cf);return j(E[3],0,cg,f)}function
aL(b,a){return r(b[3],a)[a+1][3]}function
ch(d,c,a){var
e=aL(d,c);return b(n[22],a,e)}function
ci(c,f,e){var
a=f;for(;;)try{var
g=aL(c,a),h=b(n[22],e,g);return h}catch(b){b=s(b);if(b===t){var
d=r(c[3],a)[a+1][1];if(0===d[0])throw t;var
a=d[1];continue}throw b}}function
a3(e,b){var
d=r(e[3],b)[b+1][5];if(4===d[0])return d[1];var
f=a(c[3],cj);return j(E[3],0,ck,f)}function
a4(b,a){return K(b,a)[1]}function
cl(a){return a[4]}function
cm(a){return a[5]}function
cn(e,d,c){var
a=K(e,d);a[1]=a[1]+1|0;a[2]=b(g[2][4],c,a[2]);a[3]=b(g[2][4],c,a[3]);return 0}function
co(e,d,c){var
a=K(e,d);a[1]=a[1]+1|0;a[3]=b(g[2][4],c,a[3]);return 0}var
a5=[248,cp,x.caml_fresh_oo_id(0)];function
cq(b){var
c=a(i[17][6],b[3]);return[0,b[1],b[2]+1|0,c]}function
cr(a,c,e){try{var
i=b(m[22],c,a[6]),d=i}catch(a){a=s(a);if(a!==t)throw a;var
d=g[2][1]}var
f=a[6],h=b(g[2][4],e,d);a[6]=j(m[4],c,h,f);return 0}function
ab(b,a){return r(b[3],a)[a+1][5]}function
aM(f,b){var
d=r(f[3],b)[b+1][4];if(d){var
e=d[1];return[0,e[1],e[2]]}var
g=a(c[3],cs);return j(E[3],0,ct,g)}function
a6(a,c){var
b=aM(a,c),d=b[1],e=y(a,b[2]);return[0,y(a,d),e]}function
cu(a){var
b=a[2],c=b+1|0;if(c===a[1]){var
d=((a[1]*3|0)/2|0)+1|0,e=ay(d,a1);a[1]=d;bF(i[19][10],a[3],0,e,0,b);a[3]=e}a[2]=c;return b}function
an(a){return[0,0,g[2][1],g[2][1],0,a,m[1]]}var
cw=[0,a(l[1][6],cv)],cy=[0,a(l[1][6],cx)],cz=a(o[1],2),cA=[0,0,a(o[1],2),cz],cB=a(o[10],cA);function
H(b){switch(b[0]){case
0:return b[1];case
1:var
h=b[1],e=[0,cy,a(o[5],b[2]),cB],f=a(o[11],e),g=[0,cw,a(o[5],h),f];return a(o[11],g);case
2:return a(o[2],b[1]);case
3:var
i=b[1],d=[0,H(b[2]),0],c=i;for(;;){if(3===c[0]){var
k=c[1],d=[0,H(c[2]),d],c=k;continue}var
j=[0,H(c),d];return a(a7[58],j)}default:return a(o[21],b[1][1])}}function
a8(q,p){var
f=a(e[bJ][1],p);function
d(b){return a8(q,a(e[8],b))}var
c=a(o[26],f);switch(c[0]){case
6:var
r=c[2],s=c[1],t=d(c[3]),u=[0,s,d(r),t];return a(o[10],u);case
7:var
v=c[2],w=c[1],x=d(c[3]),y=[0,w,d(v),x];return a(o[11],y);case
8:var
z=c[3],A=c[2],B=c[1],C=d(c[4]),D=d(z),E=[0,B,d(A),D,C];return a(o[12],E);case
9:var
F=c[1],G=b(i[19][52],d,c[2]),H=[0,d(F),G];return a(o[13],H);case
10:var
g=c[1],I=g[2],J=a(l[17][6],g[1]),K=[0,a(l[17][2],J),I];return a(o[16],K);case
11:var
h=c[1],j=h[1],L=h[2],M=j[2],N=a(l[23][6],j[1]),O=[0,[0,a(l[23][2],N),M],L];return a(o[19],O);case
12:var
k=c[1],m=k[1],n=m[1],P=k[2],Q=m[2],R=n[2],S=a(l[23][6],n[1]),T=[0,[0,[0,a(l[23][2],S),R],Q],P];return a(o[21],T);case
16:var
U=c[2],V=c[1],W=function(b){var
c=a(l[17][6],b);return a(l[17][2],c)},X=b(l[bN][10],W,V),Y=[0,X,d(U)];return a(o[17],Y);default:return f}}function
aN(b,a){if(0===a[0]){var
d=a[2],e=a[1],f=function(c,a){return[3,a,aN(b,c)]};return j(i[17][19],f,d,e)}var
c=a[1]-1|0;return r(b,c)[c+1]}function
L(f,d){var
g=a(c[3],cD),h=H(ab(f,d)),i=a(e[8],h),j=a(C[aB],i),k=a(c[3],cE),l=a(c[16],d),m=a(c[3],cF),n=b(c[12],m,l),o=b(c[12],n,k),p=b(c[12],o,j);return b(c[12],p,g)}function
ao(d){var
f=a(c[3],cG),g=H(d),h=a(e[8],g),i=a(C[aB],h),j=a(c[3],cH),k=b(c[12],j,i);return b(c[12],k,f)}function
O(d,f){var
h=d[1];try{var
k=b(W[7],h[6],f);return k}catch(k){k=s(k);if(k===t){var
c=cu(h),q=H(f),u=a(e[8],q),w=j(P[1],d[13],d[14],u),i=a8(d[14],w);switch(f[0]){case
2:var
B=n[1],l=[0,[0,an(i)],-1,B,0,f];break;case
3:var
C=f[2],o=O(d,f[1]),p=O(d,C);cn(h,y(h,o),c);co(h,y(h,p),c);d[3]=b(g[2][4],c,d[3]);var
D=n[1],l=[0,[0,an(i)],-1,D,[0,[0,o,p]],f];break;case
4:var
E=f[1];b(v[3],[0,c,[0,[0,c,0]]],d[5]);b(v[3],[0,c,[1,[0,c,E[2],0]]],d[5]);var
F=n[1],l=[0,[0,an(i)],-1,F,0,f];break;default:b(v[3],[0,c,[0,[0,c,0]]],d[5]);var
x=n[1],l=[0,[0,an(i)],-1,x,0,f]}r(h[3],c)[c+1]=l;j(W[5],h[6],f,c);try{var
A=b(G[7],d[12],i),m=A}catch(a){a=s(a);if(a!==t)throw a;var
m=g[2][1]}var
z=b(g[2][4],c,m);j(G[10],d[12],i,z);return c}throw k}}function
a9(a,e,d,c){var
f=O(a,d),g=O(a,c);b(v[3],[0,f,g,[0,e,0]],a[4]);return j(G[5],a[1][4],e,[0,d,c])}function
a_(a,d,c,b){var
e=O(a,c),f=O(a,b);a[6]=[0,[0,e,f,d],a[6]];return 0}function
cI(b,d,c,a){b[7]=[0,[0,d,c,a[1],a[3],a[2],a[5],a[4]],b[7]];return 0}function
cJ(a,d,c){try{var
e=a[1],f=function(a){return y(e,a)},g=b(i[19][15],f,c),h=b(aK[9],a[9],d),k=function(b){function
c(c,b){return c===y(a[1],b)?1:0}return j(i[19][32],c,g,b)},l=b(i[17][26],k,h);return l}catch(a){a=s(a);if(a===t)return 0;throw a}}function
cV(e,b,a,d){var
c=r(e[3],b)[b+1];c[1]=[1,a,d];c[2]=a;return 0}function
a$(g,f,e){var
a=f,b=e;for(;;){var
c=r(g[3],a)[a+1][1];if(0===c[0])return b;var
d=c[1],h=[0,[0,[0,a,d],c[2]],b],a=d,b=h;continue}}function
cW(c,i,h){var
o=y(c,h);if(y(c,i)===o){var
p=a$(c,h,0),a=[0,a$(c,i,0),p];for(;;){var
b=a[1];if(b){var
d=a[2];if(d){var
f=d[1][1],g=b[1][1],e=g[1]===f[1]?1:0,m=d[2],n=b[2],j=f[2],k=g[2],l=e?k===j?1:0:e;if(l){var
a=[0,n,m];continue}return a}return[0,b,0]}return[0,0,a[2]]}}throw[0,ba,cX]}function
bb(d,h,k,w){A(function(o){var
e=a(c[3],cY),f=L(d[1],k),g=a(c[3],cZ),i=L(d[1],h),j=a(c[3],c0),l=b(c[12],j,i),m=b(c[12],l,g),n=b(c[12],m,f);return b(c[12],n,e)});var
i=K(d[1],h),e=K(d[1],k);cV(d[1],h,k,w);try{var
H=b(G[7],d[12],i[5]),p=H}catch(a){a=s(a);if(a!==t)throw a;var
p=g[2][1]}var
x=b(g[2][6],h,p);j(G[10],d[12],i[5],x);var
q=b(g[2][7],i[3],e[3]);e[1]=a(g[2][20],q);e[3]=q;e[2]=b(g[2][7],i[2],e[2]);b$(d[2],i[3]);d[3]=b(g[2][7],d[3],i[3]);var
y=r(d[1][3],h)[h+1][3];function
z(c,a){return b(v[3],[0,a,[1,c]],d[5])}b(n[10],z,y);var
B=i[6];function
C(c){function
e(a){return b(v[3],[0,a,[0,c]],d[5])}return a(g[2][13],e)}b(m[10],C,B);var
l=i[4],f=e[4];if(typeof
l==="number"){if(0===l)return 0;if(typeof
f==="number"){if(0===f){e[4]=1;return 0}}else
if(0===f[0]){d[8]=b(g[2][6],k,d[8]);e[4]=1;return 0}}else
if(0===l[0]){var
D=l[1];if(typeof
f==="number"){if(0===f){e[4]=[0,D];d[8]=b(g[2][6],h,d[8]);d[8]=b(g[2][4],k,d[8]);return 0}var
u=0}else
var
u=1===f[0]?1:0;if(!u){d[8]=b(g[2][6],h,d[8]);return 0}}else{var
o=l[1],E=o[2],F=o[1];if(typeof
f==="number"){if(0===f){e[4]=[1,o];return 0}}else
if(0!==f[0])return b(v[3],[0,F,[1,E]],d[5])}return 0}function
c1(e,f){A(function(n){var
d=a(c[3],c2),g=L(f[1],e[2]),h=a(c[3],c3),i=L(f[1],e[1]),j=a(c[3],c4),k=b(c[12],j,i),l=b(c[12],k,h),m=b(c[12],l,g);return b(c[12],m,d)});var
g=f[1],h=y(g,e[1]),i=y(g,e[2]),j=1-(h===i?1:0);if(j){var
l=a4(g,i);if(a4(g,h)<l)return bb(f,h,i,e);var
d=e[3],k=typeof
d==="number"?0:0===d[0]?[0,d[1],1-d[2]]:[1,d[3],d[4],d[1],d[2],d[5]];return bb(f,i,h,[0,e[2],e[1],k])}return j}function
c9(f,s,d){A(function(j){var
e=a(c[3],c_),g=L(d[1],f),h=a(c[3],c$),i=b(c[12],h,g);return b(c[12],i,e)});var
p=y(d[1],f),h=K(d[1],p);if(0===s[0]){cr(h,s[1],f);d[3]=b(g[2][7],h[2],d[3]);return 0}var
e=s[1],q=r(d[1][3],p)[p+1];if(1-b(n[3],e,q[3]))q[3]=j(n[4],e,f,q[3]);var
i=h[4];if(typeof
i==="number"){if(0===i)return 0===e[2]?(h[4]=[1,[0,f,e]],0):(d[3]=b(g[2][7],h[2],d[3]),h[4]=[0,e],d[8]=b(g[2][4],p,d[8]),0)}else
if(1===i[0]){var
t=i[1],k=t[2],u=t[1];if(e[1]===k[1]){var
x=a3(d[1],e[1]),o=x[3],m=k[3],l=e[3];for(;;){var
w=0<o?1:0;if(w){if(m)if(l){var
z=l[2],B=m[2];b(v[3],[0,m[1],l[1],[1,u,k,f,e,o]],d[4]);var
o=o-1|0,m=B,l=z;continue}var
C=a(c[3],c7);return j(E[3],0,c8,C)}return w}}throw[0,a5,u,k,f,e]}d[3]=b(g[2][7],h[2],d[3]);return 0}function
da(e){var
g=e[1];function
h(f){if(f){var
d=f[1],k=f[2],l=y(g,d[2]);if(y(g,d[1])===l)var
j=a(c[3],db),i=[0,d];else
var
m=h(k),j=a(c[3],df),i=m;A(function(p){var
f=a(c[3],dc),g=L(e[1],d[2]),h=a(c[3],dd),i=L(e[1],d[1]),k=a(c[3],de),l=b(c[12],k,i),m=b(c[12],l,h),n=b(c[12],m,g),o=b(c[12],n,f);return b(c[12],o,j)});return i}return 0}return h(e[6])}var
dh=a(l[1][6],dg);function
dl(d){var
f=d[8];function
h(p){var
h=K(d[1],p)[4];if(typeof
h!=="number"&&0===h[0]){var
f=h[1],w=H(ab(d[1],f[1])),x=a(e[8],w),y=j(P[1],d[13],d[14],x),z=a(e[bJ][1],y),A=f[3],B=function(a){return H(ab(d[1],a))},C=b(i[17][15],B,A),D=a(i[17][9],C),F=b(a7[75],z,D),G=f[2],l=ab(d[1],p),m=F,k=G;for(;;){if(0<k){var
n=a(o[60],m),t=n[3],u=a(e[8],n[2]),q=a(bc[10],d[13]),r=a(bc[29],q),g=b(di[25],dh,r);d[13]=b(e[111],[0,g,u],d[13]);var
v=[0,a(o[2],g),0],l=[3,l,[2,g]],m=b(dk[13],v,t),k=k-1|0;continue}d[1][5]=[0,f,d[1][5]];O(d,l);return 0}}var
s=a(c[3],dj);return j(E[3],0,0,s)}return b(g[2][13],h,f)}function
bd(c){var
a=[0,m[1]],f=c[1],d=c[1][3];function
e(c,h){var
d=c<f[2]?1:0;if(d){var
e=h[1];if(0===e[0]){var
i=e[1][6],k=function(d,k){try{var
i=b(m[22],d,a[1]),e=i}catch(a){a=s(a);if(a!==t)throw a;var
e=g[2][1]}var
f=a[1],h=b(g[2][4],c,e);a[1]=j(m[4],d,h,f);return 0};return b(m[10],k,i)}return 0}return d}b(i[19][14],e,d);return a[1]}function
be(q,p,d){var
c=a(i[22][9],d),l=c[3];if(l){var
e=l[2],u=l[1],f=u[2],h=u[1],j=q[1];if(0===h[0]){var
k=h[2],n=h[1];if(k){var
A=k[2],B=k[1];try{var
C=b(W[7],j[6],n),D=[0,C,a(i[17][1],k)],E=K(j,f)[6],F=b(m[22],D,E),G=function(g){var
f=a6(q[1],g),h=[0,[0,[0,n,A],f[1]],[0,[0,B,f[2]],e]],j=c[2],k=[0,a(i[19][8],c[1]),j,h];return b(i[22][3],k,d)},H=b(g[2][13],G,F);return H}catch(a){a=s(a);if(a===t)return 0;throw a}}try{var
v=y(j,b(W[7],j[6],n))===f?1:0,I=v?b(i[22][3],[0,c[1],c[2],e],d):v;return I}catch(a){a=s(a);if(a===t)return 0;throw a}}var
o=h[1],w=o-1|0;if(0<=r(c[1],w)[w+1]){var
x=o-1|0;return r(c[1],x)[x+1]===f?b(i[22][3],[0,c[1],c[2],e],d):0}var
z=o-1|0;r(c[1],z)[z+1]=f;return b(i[22][3],[0,c[1],c[2],e],d)}p[1]=[0,[0,c[2],c[1]],p[1]];return 0}function
aP(d,c){if(0===c[0]){var
e=c[1],f=a(i[17][1],c[2]);return[0,b(W[7],d,e),f]}return b(E[9],0,dm)}function
bf(c){var
k=c[1][6],f=a(i[22][2],0),l=bd(c);function
d(a){var
h=a[5];if(typeof
h==="number")if(0===h)try{var
x=aP(k,a[4]),y=b(m[22],x,l),d=y}catch(a){a=s(a);if(a!==t)throw a;var
d=g[2][1]}else
var
d=g[2][1];else{var
z=h[1];try{var
A=b(G[7],c[12],z),o=A}catch(a){a=s(a);if(a!==t)throw a;var
o=g[2][1]}var
d=o}function
p(c){return b(i[22][3],[0,ay(a[3],-1),a,[0,[0,a[4],c],0]],f)}b(g[2][13],p,d);var
j=a[7];if(typeof
j==="number")if(0===j)try{var
r=aP(k,a[6]),u=b(m[22],r,l),e=u}catch(a){a=s(a);if(a!==t)throw a;var
e=g[2][1]}else
var
e=g[2][1];else{var
v=j[1];try{var
w=b(G[7],c[12],v),n=w}catch(a){a=s(a);if(a!==t)throw a;var
n=g[2][1]}var
e=n}function
q(c){return b(i[22][3],[0,ay(a[3],-1),a,[0,[0,a[6],c],0]],f)}return b(g[2][13],q,e)}b(i[17][14],d,c[7]);return f}function
bg(b){var
d=[0,0],e=bf(b);A(function(b){return a(c[3],dn)});try{for(;;){a(aO[3],0);be(b,d,e);continue}}catch(a){a=s(a);if(a===i[22][1])return d[1];throw a}}function
aQ(w,d){A(function(b){return a(c[3],dp)});try{for(;;){a(aO[3],0);try{c1(a(v[5],d[4]),d);var
M=1,h=M}catch(e){e=s(e);if(e!==v[1])throw e;try{var
u=a(v[5],d[5]);c9(u[1],u[2],d);var
J=1,h=J}catch(e){e=s(e);if(e!==v[1])throw e;try{var
f=a(g[2][26],d[3]);d[3]=b(g[2][6],f,d[3]);A(function(i){return function(j){var
e=a(c[3],c5),f=L(d[1],i),g=a(c[3],c6),h=b(c[12],g,f);return b(c[12],h,e)}}(f));var
l=a6(d[1],f),p=l[1],y=aM(d[1],f)[2],q=K(d[1],p),r=q[4],X=typeof
r==="number"?0:0===r[0]?(q[4]=1,d[8]=b(g[2][6],p,d[8]),1):0,z=aL(d[1],p),B=function(c,e){return function(a,f){return b(v[3],[0,e,[1,[0,a[1],a[2]-1|0,[0,c,a[3]]]]],d[5])}}(y,f);b(n[10],B,z);var
D=q[6],F=function(c){return function(a,e){return b(v[3],[0,c,[0,[0,a[1],a[2]+1|0]]],d[5])}}(f);b(m[10],F,D);try{var
G=b9(l,d[2]);b(v[3],[0,f,G,0],d[4])}catch(a){a=s(a);if(a!==t)throw a;b6(f,l,d[2])}var
I=1,h=I}catch(a){a=s(a);if(a!==t)throw a;var
h=0}}}if(h)continue;var
x=da(d);if(x)var
S=x[1],T=w?[1,S]:0,k=[0,T];else
if(a(g[2][2],d[8]))if(0<d[10]){var
U=bg(d),V=function(q){var
m=q[2],f=q[1];a(aO[3],0);var
n=0<d[10]?1:0;if(n){if(cJ(d,f[1],m))return A(function(b){return a(c[3],cK)});j(aK[5],d[9],f[1],m);var
t=d[1],r=function(b){try{var
e=ab(t,b);return e}catch(b){b=s(b);if(a(E[20],b)){var
d=a(c[3],cC);return j(E[3],0,0,d)}throw b}},l=b(i[19][15],r,m),u=a(o[2],f[1]),p=b(i[19][15],H,l);a(i[19][41],p);var
g=a(o[13],[0,u,p]),h=aN(l,f[4]),k=aN(l,f[6]);d[11]=1;d[10]=d[10]-1|0;return f[2]?(A(function(B){var
f=a(c[3],cL),i=ao(k),j=a(c[3],cM),l=ao(h),m=a(c[3],cN),n=a(e[8],g),o=a(C[aB],n),p=a(c[3],cO),q=b(c[12],p,o),r=b(c[12],q,m),s=b(c[12],r,l),t=b(c[12],s,j),u=b(c[12],t,i),v=b(c[12],u,f),w=a(c[5],0),x=a(c[16],d[10]),y=a(c[3],cP),z=b(c[12],y,x),A=b(c[12],z,w);return b(c[12],A,v)}),a9(d,g,h,k)):(A(function(B){var
f=a(c[3],cQ),i=ao(k),j=a(c[3],cR),l=ao(h),m=a(c[3],cS),n=a(e[8],g),o=a(C[aB],n),p=a(c[3],cT),q=b(c[12],p,o),r=b(c[12],q,m),s=b(c[12],r,l),t=b(c[12],s,j),u=b(c[12],t,i),v=b(c[12],u,f),w=a(c[5],0),x=a(c[16],d[10]),y=a(c[3],cU),z=b(c[12],y,x),A=b(c[12],z,w);return b(c[12],A,v)}),a_(d,[0,g],h,k))}return n};b(i[17][14],V,U);var
W=d[11]?(d[11]=0,aQ(1,d)):(A(function(b){return a(c[3],dq)}),0),k=W}else{A(function(b){return a(c[3],dr)});var
k=0}else{A(function(b){return a(c[3],ds)});dl(d);var
k=aQ(0,d)}return k}}catch(a){a=s(a);if(a[1]===a5){var
N=a[5],O=a[4],P=a[3],Q=a[2],R=w?[0,[0,Q,P,O,N]]:0;return[0,R]}throw a}}var
f=[0,[0,m[1],m[2],m[3],m[4],m[5],m[6],m[7],m[8],m[9],m[10],m[11],m[12],m[13],m[14],m[15],m[16],m[17],m[18],m[19],m[20],m[21],m[22],m[23],m[24]],[0,n[1],n[2],n[3],n[4],n[5],n[6],n[7],n[8],n[9],n[10],n[11],n[12],n[13],n[14],n[15],n[16],n[17],n[18],n[19],n[20],n[21],n[22],n[23],n[24]],G,W,aI,H,A,ce,cl,cm,cd,O,a9,a_,cI,cq,y,ch,ci,ab,a3,aM,cW,bd,be,bf,aP,bg,aQ,L,a2];ak(160,f,"Cc_plugin.Ccalgo");function
ag(a){return[0,a,a,[2,a]]}function
ac(b,a){var
c=b[3],d=a[3];if(2===c[0])if(2===d[0])return ag([3,c[1],d[1]]);return[0,[3,b[1],a[1]],[3,b[2],a[2]],[4,b,a]]}function
B(o,n){var
e=o,d=n;for(;;){var
g=e[3],h=d[3];switch(g[0]){case
2:return d;case
4:var
l=g[2],m=g[1];switch(h[0]){case
2:var
i=0;break;case
3:var
k=h[1][3];if(4===k[0]){var
r=h[2],s=k[1],t=B(l,k[2]),e=ac(B(m,s),t),d=r;continue}var
i=1;break;case
4:var
u=h[1],v=B(l,h[2]);return ac(B(m,u),v);default:var
i=1}break;default:var
i=0}if(!i){if(2===h[0])return e;if(3===g[0]){var
q=g[1],e=q,d=B(g[2],d);continue}}if(b(f[5],e[2],d[1]))return[0,e[1],d[2],[3,e,d]];var
p=a(c[3],dt);return j(E[3],0,0,p)}}function
M(b){var
a=b[3];switch(a[0]){case
0:return[0,b[2],b[1],[1,a[1]]];case
1:return[0,b[2],b[1],[0,a[1]]];case
2:return b;case
3:var
c=a[2],d=M(a[1]);return B(M(c),d);case
4:var
e=a[1],f=M(a[2]);return ac(M(e),f);default:var
g=a[4],h=a[3],i=a[2],j=[5,M(a[1]),i,h,g];return[0,b[2],b[1],j]}}function
bh(d,a){var
c=b(f[3][7],d,a);return[0,c[1],c[2],[0,a]]}function
bi(d,a){var
c=b(f[3][7],d,a);return[0,c[2],c[1],[1,a]]}function
bj(f,e){var
b=f,d=e;for(;;){if(3===b[0]){var
h=b[2],i=b[1];if(0<d){var
b=i,d=d-1|0;continue}return h}var
g=a(c[3],du);return j(E[3],0,dv,g)}}function
bk(c,d,b,a){var
e=bj(c[2],b-a|0);return[0,bj(c[1],b-a|0),e,[5,c,d,b,a]]}function
Q(d,e,g){function
i(n){var
h=b(f[30],d,g),i=a(c[4],dw),j=b(f[30],d,e),k=a(c[3],dx),l=b(c[12],k,j),m=b(c[12],l,i);return b(c[12],m,h)}a(f[7],i);if(e===g)return ag(b(f[20],d,e));var
h=j(f[23],d,e,g),k=h[1],l=M(ap(d,g,h[2]));return B(ap(d,e,k),l)}function
bl(d,i){var
g=i[2],j=i[1],k=j[2],l=j[1];function
p(n){var
e=b(f[30],d,k),g=a(c[4],dy),h=b(f[30],d,l),i=a(c[3],dz),j=b(c[12],i,h),m=b(c[12],j,g);return b(c[12],m,e)}a(f[7],p);var
q=Q(d,l,g[1]),r=M(Q(d,k,g[2])),e=g[3];if(typeof
e==="number")var
h=bm(d,g[1],g[2]);else
if(0===e[0])var
m=e[1],s=e[2]?bi(a(f[9],d),m):bh(a(f[9],d),m),h=s;else
var
n=e[2],t=e[5],u=aS(d,e[1],n,e[3],e[4]),o=b(f[21],d,n[1]),h=bk(u,o[1],o[3],t);return B(B(q,h),r)}function
aR(d,g,e){function
l(k){var
e=a(c[4],dA),h=b(f[30],d,g),i=a(c[3],dB),j=b(c[12],i,h);return b(c[12],j,e)}a(f[7],l);var
h=j(f[19],d,g,e),i=Q(d,g,h);if(0===e[3])return i;var
m=a(f[16],e),k=b(f[22],d,h),n=k[1],o=b(f[20],d,k[2]),p=aR(d,n,m);return B(i,ac(p,ag(o)))}function
ap(e,g,d){function
i(u){var
h=a(c[3],dC);function
i(b){return a(c[16],b[1][2])}function
k(b){return a(c[3],dD)}var
l=j(c[39],k,i,d),m=a(c[3],dE),n=a(c[4],dF),o=b(f[30],e,g),p=a(c[3],dG),q=b(c[12],p,o),r=b(c[12],q,n),s=b(c[12],r,m),t=b(c[12],s,l);return b(c[12],t,h)}a(f[7],i);if(d){var
h=d[1],k=d[2],l=bl(e,h);return B(ap(e,h[1][2],k),l)}return ag(b(f[20],e,g))}function
bm(d,g,e){function
j(n){var
h=b(f[30],d,e),i=a(c[4],dH),j=b(f[30],d,g),k=a(c[3],dI),l=b(c[12],k,j),m=b(c[12],l,i);return b(c[12],m,h)}a(f[7],j);var
h=b(f[22],d,g),k=h[2],l=h[1],i=b(f[22],d,e),m=i[1],n=Q(d,k,i[2]);return ac(Q(d,l,m),n)}function
aS(d,g,i,e,h){function
j(n){var
h=b(f[30],d,e),i=a(c[4],dJ),j=b(f[30],d,g),k=a(c[3],dK),l=b(c[12],k,j),m=b(c[12],l,i);return b(c[12],m,h)}a(f[7],j);var
k=Q(d,g,e),l=aR(d,g,i),m=B(k,aR(d,e,h));return B(M(l),m)}var
aq=[0,ag,ac,B,M,bh,bi,bk,Q,bl,ap,bm,aS,function(c,b){if(bG<=b[1]){var
a=b[2];return aS(c,a[1],a[2],a[3],a[4])}var
d=b[2];return Q(c,d[1],d[2])}];ak(161,aq,"Cc_plugin.Ccproof");function
X(b,a){return[N,function(c){return j(aT[2],dL,b,a)}]}var
aU=X(dN,dM),dQ=X(dP,dO),bn=X(dS,dR),dV=X(dU,dT),bo=X(dX,dW),w=X(dZ,dY),R=X(d1,d0);function
bp(c,b,a){return z(br[16],bq[14],c,b,a)}function
ar(c,b,a){return z(br[16],bq[9],c,b,a)}function
as(c,b,a){return j(P[4],c,[0,b],a)}function
D(f,c,z){var
g=z;for(;;){var
A=bp(f,c,g),d=b(e[3],c,A);switch(d[0]){case
6:var
m=d[3],n=d[2];if(j(e[aE][13],c,1,m)){var
p=a(C[47],m),B=as(f,c,p),E=as(f,c,n),F=D(f,c,p);return[3,[3,[1,E,B],D(f,c,n)],F]}break;case
9:var
G=d[2],H=D(f,c,d[1]),I=function(a){return D(f,c,a)},J=b(i[19][15],I,G),K=function(b,a){return[3,b,a]};return j(i[19][17],K,H,J);case
10:var
q=d[1],L=q[1],M=b(e[2][2],c,q[2]),N=a(l[17][6],L),O=[0,a(l[17][2],N),M];return[0,a(o[16],O)];case
11:var
r=d[1],s=r[1],P=s[2],Q=s[1],R=b(e[2][2],c,r[2]),S=a(l[23][6],Q),T=[0,[0,a(l[23][2],S),P],R];return[0,a(o[19],T)];case
12:var
u=d[1],v=u[1],w=v[2],x=v[1],U=x[2],V=x[1],W=b(e[2][2],c,u[2]),X=a(l[23][6],V),h=[0,a(l[23][2],X),U],Y=a(d2[27],h)[1],y=b(d3[44],f,[0,h,w]);return[4,[0,[0,[0,h,w],W],y,y-Y[6]|0]];case
16:var
Z=d[2],_=d[1],$=function(b){var
c=a(l[17][6],b);return a(l[17][2],c)},aa=b(l[bN][10],$,_),g=bF(d4[9],f,c,aa,Z,0);continue}var
k=b(C[60],c,g);if(b(e[aE][16],c,k))return[0,b(e[5],c,k)];throw t}}function
aV(d,c,g){var
k=ar(d,c,g),h=b(e[3],c,k);if(9===h[0]){var
f=h[2],i=T(w),l=h[1],m=U===i?w[1]:N===i?a(S[2],w):w;if(j(C[al],c,m,l))if(3===f.length-1){var
n=D(d,c,r(f,2)[3]),o=D(d,c,r(f,1)[2]);return[0,aA,[0,r(f,0)[1],o,n]]}return[0,aY,D(d,c,g)]}return[0,aY,D(d,c,g)]}function
ah(d,c,h){var
r=bp(d,c,h),f=b(e[3],c,r);switch(f[0]){case
0:var
k=f[1];return[0,[1,k],a(g[2][5],k)];case
6:var
l=f[3],m=f[2];if(j(e[aE][13],c,1,l)){var
n=a(C[47],l),o=ah(d,c,m),t=o[2],u=o[1],p=ah(d,c,n),v=p[2],w=p[1],x=as(d,c,n),y=as(d,c,m);return[0,[0,[1,y,x],[0,u,[0,w,0]]],b(g[2][7],t,v)]}break;case
9:var
z=f[2],A=D(d,c,f[1]),B=function(a){return ah(d,c,a)},E=b(i[19][49],B,z),q=a(i[17][44],E),F=q[1],G=j(i[17][18],g[2][7],g[2][1],q[2]);return[0,[0,A,a(i[17][9],F)],G]}var
s=D(d,c,h);return[0,[0,s,0],g[2][1]]}function
bs(a){return 0===a[0]?1:0}function
bt(k,c,i,v){try{var
x=ar(k,c,v),l=b(e[73],c,x)}catch(a){a=s(a);if(a===o[54])throw t;throw a}var
d=l[2],m=T(w),y=l[1],z=U===m?w[1]:N===m?a(S[2],w):w;if(j(C[al],c,z,y))if(3===d.length-1){var
n=ah(k,c,r(d,1)[2]),p=n[1],A=n[2],q=ah(k,c,r(d,2)[3]),u=q[1],B=q[2];if(a(g[2][20],A)===i)if(bs(p))var
f=0;else
var
E=r(d,0)[1],f=[0,b(e[5],c,E)];else
var
f=1;if(a(g[2][20],B)===i)if(bs(u))var
h=0;else
var
D=r(d,0)[1],h=[0,b(e[5],c,D)];else
var
h=1;if(1===f)if(1===h)throw t;return[0,i,f,p,h,u]}throw t}function
d5(o,c,n,m){var
d=o,f=n,h=m;for(;;){var
p=ar(d,c,h),g=b(e[3],c,p);if(6===g[0]){var
i=g[3],k=g[2],l=T(R),q=g[1],r=U===l?R[1]:N===l?a(S[2],R):R;if(j(C[al],c,r,i))return[0,bP,bt(d,c,f,k)];var
d=b(e[bV],[0,q,k],d),f=f+1|0,h=i;continue}return[0,bH,bt(d,c,f,h)]}}function
d6(d,c,g){var
n=ar(d,c,g),f=b(e[3],c,n);if(6===f[0]){var
k=f[3],l=f[2],m=T(R),o=f[1],p=U===m?R[1]:N===m?a(S[2],R):R;if(j(C[al],c,p,k)){var
h=aV(d,c,l);if(aA<=h[1]){var
i=h[2];return[0,bK,[0,i[1],i[2],i[3]]]}return[0,bU,h[2]]}try{var
q=d5(b(e[bV],[0,o,l],d),c,1,k);return q}catch(a){a=s(a);if(a===t)return[0,aY,D(d,c,g)];throw a}}return aV(d,c,g)}function
Y(c,g,f){var
d=T(c);function
h(b){return a(f,a(e[21],[0,b,g]))}var
i=U===d?c[1]:N===d?a(S[2],c):c,j=a(q[66][59],i);return b(k[71][1],j,h)}function
ai(c,n,w){function
d(h){var
d=T(c);function
f(o){var
q=a(k[66][5],h),x=a(k[66][3],h);function
c(r){var
y=b(p[42][8],h,o),A=a(i[19][11],n),B=j(C[58],r,y,A),c=r,k=B,f=w,d=0,D=a(e[21],[0,o,n]);for(;;){if(0===f){var
E=[0,D,a(i[17][9],d)],s=a(e[34],E),t=[0,c];z(P[5],q,t,s,x);return[0,t[1],s]}var
g=b(e[3],c,k);if(6===g[0]){var
u=g[3],l=fd(d9[4],q,c,0,0,0,0,0,0,g[2]),m=l[2],v=l[1],c=v,k=b(e[aE][5],m,u),f=f-1|0,d=[0,m,d];continue}throw[0,ba,d8]}}return b(d_[2],0,c)}var
g=U===d?c[1]:N===d?a(S[2],c):c,l=a(q[66][59],g);return b(k[71][1],l,f)}return a(k[66][10],d)}function
at(d,c){function
e(e){var
f=P[2];function
g(a){return b(f,0,a)}var
h=j(p[42][1],g,e,c)[1],i=b(F[136],d,c),l=a(k[64][1],h);return b(k[18],l,i)}return a(k[66][10],e)}function
bw(c,b,a){return az(bx[5],[0,eb[112]],0,ea,d$,c,b,a)}function
I(f,e){function
c(c){var
g=a(k[66][5],c),d=bw(g,a(p[42][4],c),f),h=d[1],i=a(e,d[2]),j=a(k[64][1],h);return b(k[18],j,i)}return a(k[66][10],c)}function
u(b){var
c=a(f[6],b);return a(e[8],c)}function
J(j){function
d(i){function
f(a){return b(p[42][7],i,a)}try{var
d=j[3];switch(d[0]){case
0:var
D=a(e[8],d[1]),g=a(F[45],D);break;case
1:var
E=a(e[8],d[1]),w=u(j[1]),G=u(j[2]),H=function(a){return Y(dV,[0,a,G,w,E],F[45])},g=I(f(w),H);break;case
2:var
x=d[1],K=u(x),L=function(a){var
b=F[45];return Y(bn,[0,a,u(x)],b)},g=I(f(K),L);break;case
3:var
y=d[2],o=d[1],M=u(o[1]),z=u(o[2]),N=u(y[2]),O=function(a){var
c=ai(bo,[0,a,M,z,N],2),d=[0,J(y),0],e=[0,J(o),d];return b(q[66][19],c,e)},g=I(f(z),O);break;case
4:var
r=d[2],t=d[1],m=u(t[1]),h=u(r[1]),n=u(t[2]),A=u(r[2]),P=function(g){function
d(j){function
d(d){var
f=a(l[1][6],ec),k=b(p[42][11],f,i),o=[0,a(e[9],1),[0,h]],s=[0,[0,k],g,a(e[21],o)],u=ai(aU,[0,g,d,a(e[19],s),m,n],1),v=ai(aU,[0,j,d,n,h,A],1),w=a(e[21],[0,n,[0,A]]),x=a(e[21],[0,n,[0,h]]),y=ai(bo,[0,d,a(e[21],[0,m,[0,h]]),x,w],2),z=a(c[3],ed),B=[0,b(q[66][5],0,z),0],C=[0,F[122],B],D=J(r),E=[0,b(q[66][3],v,D),C],G=[0,a(q[66][24],E),0],H=J(t),I=[0,b(q[66][3],u,H),G];return b(q[66][19],y,I)}return I(f(a(e[21],[0,m,[0,h]])),d)}return I(f(h),d)},g=I(f(m),P);break;default:var
v=d[1],Q=d[4],R=d[3],S=d[2],B=u(v[1]),T=u(v[2]),C=u(j[1]),U=a(e[9],(1+R|0)-Q|0),V=function(c){function
d(o){var
f=S[1][2],d=a(p[42][4],i),g=a(e[9],1),h=a(p[42][5],i),j=az(bv[38],h,d,f,g,c,U,C),m=a(l[1][6],d7),n=[0,[0,b(p[42][11],m,i)],c,j],r=ai(aU,[0,c,o,a(e[19],n),B,T],1),s=J(v),t=b(q[66][3],r,s),u=a(k[64][1],d);return b(q[66][3],u,t)}return I(f(C),d)},g=I(f(B),V)}return g}catch(c){c=s(c);if(a(k[70][10],c))return b(k[21],0,c);throw c}}return a(k[66][10],d)}function
ef(c){function
d(d){var
e=P[2];function
f(a){return b(e,0,a)}var
g=j(p[42][1],f,d,c)[1],h=a(F[45],c),i=a(k[64][1],g);return b(k[18],i,h)}return a(k[66][10],d)}function
by(j,h,f,i){function
c(c){var
g=u(h),d=u(f);function
k(f){var
m=a(l[1][6],eg),h=b(p[42][11],m,c),n=a(l[1][6],eh),o=b(p[42][11],n,c),r=[0,[0,o],f,a(e[9],1)],s=a(e[19],r),t=[0,Y(dQ,[0,f,g,s,j,d,a(e[10],h)],ef),0],k=[0,f,g,d],u=[0,J(i),t],v=[0,h],x=Y(w,k,function(a){return at(v,a)});return b(q[66][19],x,u)}return I(b(p[42][7],c,d),k)}return a(k[66][10],c)}function
bz(Z,X){function
d(h){var
_=a(p[42][4],h);a(aT[3],aT[10]);function
$(b){return a(c[3],ek)}a(f[7],$);var
A=a(p[42][5],h),r=a(p[42][4],h),N=[0,a(k[66][14],h),r],d=b(f[11],Z,N),s=[0,0],B=[0,0];function
O(a){var
c=D(A,r,a);b(f[12],d,c);return 0}b(i[17][14],O,X);var
P=a(k[66][4],h);function
Q(j){var
h=a(bu[2][1][1],j),e=a(o[2],h),c=d6(A,r,a(bu[2][1][3],j)),g=c[1];if(aA<=g){if(bP<=g)return bH<=g?z(f[15],d,h,1,c[2]):z(f[15],d,h,0,c[2]);if(bK<=g){var
k=c[2];return z(f[14],d,[0,e],k[2],k[3])}var
l=c[2];return z(f[13],d,e,l[2],l[3])}if(bU<=g){var
m=c[2],p=s[1],q=function(a){return z(f[14],d,[2,a[1],e],a[2],m)};b(i[17][14],q,p);B[1]=[0,[0,e,m],B[1]];return 0}var
n=c[2],t=B[1];function
u(a){return z(f[14],d,[2,e,a[1]],n,a[2])}b(i[17][14],u,t);s[1]=[0,[0,e,n],s[1]];return 0}b(i[17][14],Q,P);var
C=aV(A,r,a(p[42][6],h));if(aA<=C[1]){var
H=C[2];z(f[14],d,0,H[2],H[3])}else{var
R=C[2],S=s[1],T=function(a){return z(f[14],d,[1,a[1]],a[2],R)};b(i[17][14],T,S)}function
aa(b){return a(c[3],el)}a(f[7],aa);var
K=b(f[29],1,d);function
ab(b){return a(c[3],em)}a(f[7],ab);var
g=a(f[8],d);if(K){var
t=K[1],ac=function(b){return a(c[3],en)};a(f[7],ac);if(typeof
t==="number"){var
L=a(k[66][5],h),ad=a(f[10],g),ae=function(c){var
h=b(f[21],g,c[1]),j=c[3];function
k(a){return u(b(f[20],g,a))}var
l=b(i[17][17],k,j),d=h[1],m=d[1],n=c[2],o=[0,m,a(e[2][1],d[2])],p=[0,a(e[28],o),l];return[0,a(e[34],p),n]},af=b(i[17][15],ae,ad),ag=b(bA[3],0,eo),ah=function(a){var
c=a[2],d=az(eq[9],0,ep,0,l[1][10][1],L,_,a[1]);function
e(a){return ag}var
f=[4,d,b(i[17][54],c,e)],g=b(bA[3],0,f);return b(er[42],L,g)},ai=a(c[3],es);b(aH[6],0,ai);var
aj=a(c[3],et),ak=a(c[3],eu),al=function(h){var
d=a(c[3],ev),e=a(c[13],0),f=a(c[3],ew),g=b(c[12],f,e);return b(c[12],g,d)},am=j(c[39],al,ah,af),an=a(c[3],ex),ao=b(c[12],an,am),ap=b(c[12],ao,ak),ar=b(c[26],8,ap),as=a(c[3],ey),au=b(c[12],as,ar),av=b(c[12],au,aj);b(aH[6],0,av);var
aw=a(c[3],ez);return b(q[66][4],0,aw)}else{if(0===t[0]){var
v=t[1],M=v[2],E=b(aq[13],g,[0,bG,[0,v[1],M,v[3],v[4]]]);b(f[21],g,M[1]);var
W=function(c){var
d=u(E[1]),g=u(E[2]),h=a(k[66][5],c),i=a(p[42][4],c),e=bw(h,i,b(p[42][7],c,d)),j=e[2],m=e[1],n=a(l[1][6],ej),f=b(p[42][11],n,c),r=[0,a(bv[16],f),0],o=[0,j,d,g],s=[0,J(E),r],t=[0,f],y=Y(w,o,function(a){return at(t,a)}),v=b(q[66][19],y,s),x=a(k[64][1],m);return b(q[66][3],x,v)};return a(k[66][10],W)}var
n=t[1],x=b(aq[13],g,[0,-608347012,[0,n[1],n[2]]]),G=b(f[20],g,n[1]),y=b(f[20],g,n[2]),m=n[3];if(typeof
m==="number")return J(x);else
switch(m[0]){case
0:var
ax=a(e[8],m[1]),U=function(c){var
d=u(G),g=u(y),h=a(l[1][6],ee),f=b(p[42][11],h,c),i=[0,ax,[0,a(e[10],f)]],j=a(e[21],i);function
k(c){var
h=[0,a(F[99],j),0],e=[0,c,d,g],i=[0,J(x),h],k=[0,f],l=Y(w,e,function(a){return at(k,a)});return b(q[66][19],l,i)}return I(b(p[42][7],c,d),k)};return a(k[66][10],U);case
1:return by(a(e[8],m[1]),G,y,x);default:var
ay=m[2],aB=a(e[8],m[1]),aC=a(e[8],ay),V=function(d){var
f=u(y),g=a(l[1][6],ei),c=b(p[42][11],g,d),h=[0,aC,[0,a(e[10],c)]],i=a(e[21],h),j=[0,a(F[99],i),0],k=[0,by(aB,G,y,x),j],m=at([0,c],f);return b(q[66][19],m,k)};return a(k[66][10],V)}}}var
aD=a(c[3],eA);return b(q[66][4],0,aD)}return a(k[66][10],d)}var
eC=a(c[3],eB),bB=b(q[66][5],0,eC);function
bC(d,c){var
e=bz(d,c),f=a(q[66][30],F[17]),g=b(q[66][3],f,e);return b(q[66][12],g,bB)}function
eD(c,d,l,i){var
f=T(c);function
g(m){function
c(c){var
n=P[2];function
o(a){return b(n,0,a)}var
f=j(p[42][1],o,c,d),q=f[2],r=f[1],s=a(p[42][5],c),g=az(bx[5],0,0,0,eE,s,r,q),t=g[1],h=a(e[21],[0,m,[0,g[2],d,l]]),u=a(p[42][5],c),v=z(P[2],0,u,t,h)[1],w=a(i,h),x=a(k[64][1],v);return b(k[18],x,w)}return a(k[66][10],c)}var
h=U===f?c[1]:N===f?a(S[2],c):c,m=a(q[66][59],h);return b(k[71][1],m,g)}function
eF(l){var
y=a(k[66][3],l),c=a(p[42][4],l);function
z(d,c){try{var
e=0,f=F[86],g=[0],h=function(a){return Y(bn,g,a)}(f),i=[0,a(q[66][22],h),e],j=[0,a(k[16],0),i],l=eD(w,d,c,F[143]),m=b(q[66][19],l,j);return m}catch(c){c=s(c);if(a(k[70][10],c))return b(k[21],0,c);throw c}}function
A(d){var
c=d[1],e=d[2];if(c[1]!==eG[1])if(c[1]!==eH[1])return b(k[21],[0,e],c);return a(k[16],0)}var
g=b(e[3],c,y);if(9===g[0]){var
h=g[2];if(3===h.length-1){var
n=T(w),B=g[1],D=h[2],E=h[3],G=U===n?w[1]:N===n?a(S[2],w):w;if(j(C[al],c,G,B)){var
o=b(e[3],c,D),t=b(e[3],c,E);if(9===o[0])if(9===t[0]){var
v=t[2],i=o[2];if(i.length-1===v.length-1)var
x=function(c){if(0<=c){var
d=x(c-1|0),e=r(v,c)[c+1],f=z(r(i,c)[c+1],e);return b(q[66][16],f,d)}var
g=bC(aX,0);return a(q[66][22],g)},u=x(i.length-1-1|0),f=1;else
var
f=0}else
var
f=0;else
var
f=0;if(!f)var
u=a(k[16],0);var
m=u,d=1}else
var
d=0}else
var
d=0}else
var
d=0;if(!d)var
m=a(k[16],0);return b(k[23],m,A)}var
Z=[0,J,bz,bB,bC,a(k[66][10],eF)];ak(183,Z,"Cc_plugin.Cctac");a(eI[10],au);var
eJ=0;function
eK(c,a,d){return b(Z[4],c,a)}var
eM=a(l[1][7],eL),eN=[0,[0,[5,a(aw[16],av[13])]],eM],eP=[0,eO,[1,b(ax[11],0,eN),0]],eR=a(l[1][7],eQ),eS=[0,[5,a(aw[16],av[21])],eR],eU=[0,[0,[0,eT,[1,b(ax[11],0,eS),eP]],eK],eJ];function
eV(a,c){return b(Z[4],aX,a)}var
eX=a(l[1][7],eW),eY=[0,[0,[5,a(aw[16],av[13])]],eX],e1=[0,[0,[0,e0,[0,eZ,[1,b(ax[11],0,eY),0]]],eV],eU];function
e2(a,c){return b(Z[4],a,0)}var
e4=a(l[1][7],e3),e5=[0,[5,a(aw[16],av[21])],e4],e7=[0,[0,[0,e6,[1,b(ax[11],0,e5),0]],e2],e1],e9=[0,[0,e8,function(a){return b(Z[4],aX,0)}],e7];z(bD[10][8],au,e_,0,e9);var
e$=0,fb=[0,[0,fa,function(a){return Z[5]}],e$];z(bD[10][8],au,fc,0,fb);var
bE=[0,au];ak(189,bE,"Cc_plugin.G_congruence");ak(190,[0,f,aq,Z,bE],"Cc_plugin");return}
