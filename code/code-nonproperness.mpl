with(LinearAlgebra):
with(PolynomialIdeals):
with(combinat): 

################## The function is to generate likelihood equations automatically.
lle := proc(f, var, par)
local sys, i, k, newvar;
sys := [];
for i from 1 to nops(par) do
   sys := [op(sys), var[i]*(L1+add((diff(f[k], var[i]))*L||(k+1), k=1..nops(f)))-par[i]];
end do;
sys    := [op(sys), op(f), add(k, k in var)-1];
newvar := [op(var), seq(L||k, k=1..nops(f)+1)];
return sys, newvar;
end proc:

################## The function is to compute W-infinity according to LR2005 PropernessDefects.
################## Init W||i: Because of likely equations, init is empty.
wif := proc(sys, var, par)
local G, li, i, j, lc, l, W, list;
G   := fgb_gbasis(sys, 0, var, par, {"verb"=3});
li  := [];
for i from 1 to nops(var) do 
     W||i := [];
     for j from 1 to nops(G) do
     	lc := lcoeff(G[j], order = tdeg(op(var)), 'lm');
     	l  := degree(G[j], {op(var)});
     	if l<>FAIL and l>=1 and lm=var[i]^l then
     		W||i := [op(W||i), lc];
     	end if;
     end do;
     if W||i<>[1] then
        li := [op(li), i];
     end if
end do;
W    := Intersect(seq(PolynomialIdeal(op(W||i)), i in li));
W    := Generators(W);
list := factors(op(W))[2];
list := [seq(list[i][1], i=1..nops(list))];
return list;
end proc:

################## The function is to measure time of interpolating once
onetime := proc(f, var, par, N)
local sys, newvar, newsys, tt, newdlist, nondlist, key, newpar, ssys, R, A, i, l, a, st, st1;
sys, newvar := lle(f, var, par);
newsys, tt, newdlist, nondlist, key, newpar := LinearOperator(sys, newvar, par, 10);
st := time():
ssys := newsys;
R    := rand(1..N);
A    := [];
for i from 1 to nops(par) do
    if i<>key then
        a := R();
        ssys := subs(par[i]=a, ssys);
        A := [op(A), a];
    end if;
end do;
l   := wif(ssys, newvar, [par[key]]);
st1 := time()-st;    
save st1, "onetime.txt";  
end proc:

################## The function is to compute the total degree of W-infinity
ttDegree := proc(sys, var, par, N)
local newsys, R, t, i, list, d;
R      := rand(1..N);
newsys := subs(seq(par[i]=R()*t+R(), i=1..nops(par)), sys);
list   := wif(newsys, var, [t]);
d      := add(degree(list[i]), i=1..nops(list));
return d;
end proc:

################## The function is to compute the degree of each parameter in W-infinity
SubttDegree := proc(sys, var, par, j, N)
local newsys, R, i, list, d;
R := rand(1..N);
if j=1 then
    newsys := subs(seq(par[i]=R(), i=2..nops(par)), sys);
end if;
if j=nops(par) then
    newsys := subs(seq(par[i]=R(), i=1..nops(par)-1), sys);
end if;
if j>1 and j<nops(par) then
    newsys := subs(seq(par[i]=R(), i=1..j-1), seq(par[i]=R(), i=j+1..nops(par)),sys);
end if;
newsys := subs(par[j]=R()*par[j]+R(), newsys);
list   := wif(newsys, var, [par[j]]);
d      := add(degree(list[i]), i=1..nops(list));
return d;
end proc:

################## The function is to compute the degree of each parameter in the nonlinear part of W-infinity
NonSubttDegree := proc(newsys, var, par, j, N)
local newsyss, R, i, list, l, d, dn, k;
R := rand(1..N);
if j=1 then
    newsyss := subs(seq(par[i]=R(), i=2..nops(par)), newsys);
end if;
if j=nops(par) then
    newsyss := subs(seq(par[i]=R(), i=1..nops(par)-1), newsys);
end if;
if j>1 and j<nops(par) then
    newsyss := subs(seq(par[i]=R(), i=1..j-1), seq(par[i]=R(), i=j+1..nops(par)), newsys);
end if;
newsyss   := subs(par[j]=R()*par[j]+R(), newsyss);
list      := wif(newsyss, var, [par[j]]);
l         := [seq(degree(list[i], par[j]), i=1..nops(list))];
d         := add(l[i], i=1..nops(l));
dn        := 0;
k         := 0;
for i from 1 to nops(l) do
    if l[i]>1 then
       k  := k+1;
       dn := dn+l[i];
    end if;
end do;
return d, dn, k;
end proc:

################## The function is to compute linear operator. 
LinearOperator := proc(sys, var, par, N)
local tt, dlist, i, j, ds, dn, key, A, B, C, R, a, temp, newpar, newsys, newdlist, nondlist, k, klist, mk;
tt     := ttDegree(sys, var, par, 100);
dlist  := [];
for j from 1 to nops(par) do
      ds := SubttDegree(sys, var, par, j, 100);
   dlist := [op(dlist), ds];
end do;
for i from 1 to nops(dlist) do
   if  dlist[i]=max(dlist) then
         key := i;
         if dlist[i]=tt then
            klist        := [];
            nondlist     := [];
            for j from 1 to nops(par) do
                ds, dn, k  := NonSubttDegree(sys, var, par, j, 100);
                klist      := [op(klist), k];
                nondlist   := [op(nondlist), dn];
            end do; 
            if max(nondlist)>1 and min(nondlist)=0 then
               mk := max(klist);
               for i from 1 to nops(nondlist) do
                   if nondlist[i]=0 then
                      nondlist[i] := mk;
                   end if;
               end do;
            end if;
            return sys, tt, dlist, nondlist, key, par;
         else
            A := DiagonalMatrix([1$nops(par)]);
            B := Matrix(nops(par));
            B[1] := A[i];
            B[i] := A[1];
            for j from 1 to nops(par) do
                if j<>1 and j<>i then
                   B[j]  := A[j];
                end if; 
            end do;
            C := Matrix(nops(par));
            R := rand(1..N);
            for i from 2 to nops(par) do
                a         := R();
                C[i, 1]   := a;
            end do; 
            temp          := A + C;
            newpar        := B.temp.B.(Transpose(Matrix(par)));
            newsys        := subs(seq(par[i]=newpar[i, 1], i=1..nops(par)), sys);
            newdlist      := [];
            klist         := [];
            nondlist      := [];
            for j from 1 to nops(par) do
                ds, dn, k := NonSubttDegree(newsys, var, par, j, 100);
                klist     := [op(klist), k];
                newdlist  := [op(newdlist), ds];
                nondlist  := [op(nondlist), dn];
            end do; 
            if max(nondlist)>1 and min(nondlist)=0 then
               mk := max(klist);
               for i from 1 to nops(nondlist) do
                   if nondlist[i]=0 then
                      nondlist[i] := mk;
                   end if;
               end do;
            end if; 
            return newsys, tt, newdlist, nondlist, key, [seq(newpar[i, 1], i=1..nops(par))];
         end if;        
   end if;
end do;
end proc:

##################
getlis := proc(sys, var, par, N)
local newsys, R, t, i, l, r, ran, list, lis;
l||1 := N;    R := rand(l||1..9+l||1); r||1 := R();
l||2 := N+20; R := rand(l||2..9+l||2); r||2 := R();
l||3 := N+40; R := rand(l||3..9+l||3); r||3 := R();
for i from 4 to nops(par) do
    l||i := l||(i-2)+l||(i-1)+20;
    R    := rand(l||i..9+l||i);
    r||i := R();
end do;
newsys := subs(seq(par[i]=t+r||i, i=1..nops(par)), sys);
list   := wif(newsys, var, [t]);
lis    := [];
for i from 1 to nops(list) do
    if degree(list[i], t)=1 then
       lis := [op(lis), list[i]-t];
    end if;
end do;
ran    := [seq(r||i, i=1..nops(par))];
return lis, ran;
end proc:

##################
pos := proc(k, ran, par, klist)
local comb, L, Q, M, D, i, j, R;
comb  := choose(nops(par), k);
L     := [];
Q     := [];
M     := [];
D     := [];
for i from 1 to nops(comb) do
    L := [op(L), add(ran[j], j in comb[i])];
    Q := [op(Q), add(par[j], j in comb[i])];
end do;
for i from 1 to nops(klist) do
    for j from 1 to nops(L) do
        if klist[i]=L[j] then
           M := [op(M), Q[j]];
           D := [op(D), i];
           break;
        end if;
    end do;
end do;
if nops(D)>0 then
   R := subsop(seq(i=NULL, i in D), klist);
else
   R := klist;
end if; 
return M, R;
end proc:

##################
binar := proc(k, ran, par, klist)
local n, i, j, M, R, rsum, psum, new, D, newk;
n := nops(par);
if k<=trunc((1+n)/2) then
   M, R := pos(k, ran, par, klist);
   return M, R;
else
   newk := n-k;
   rsum := add(ran[i], i=1..nops(ran));
   psum := add(par[i], i=1..nops(par));
   if newk=0 then
        M := [];
        R := klist;
        for i from 1 to nops(klist) do
            if klist[i]=rsum then
               M := [psum];
               R := subsop(i=NULL, klist);
               break;
            end if;  
        end do;    
        return M, R;
   elif newk=1 then
        new := [seq(rsum-klist[i], i=1..nops(klist))];
        M   := [];
        D   := [];
        for i from 1 to nops(new) do
            for j from 1 to nops(ran) do
                if new[i]=ran[j] then
                   M := [op(M), psum-par[j]];
                   D := [op(D), i];
                   break;
                end if;
            end do;
        end do;
        if nops(D)>0 then
           R := subsop(seq(i=NULL, i in D), klist);
        else
           R := klist;
        end if;
        return M, R;
   else
        new  := [seq(rsum-klist[i], i=1..nops(klist))];
        M, R := pos(newk, ran, par, new);
        M    := [seq(psum-M[i], i=1..nops(M))];
        R    := [seq(rsum-R[i], i=1..nops(R))];
        return M, R;
   end if;
end if;
end proc:

################## The function is to compute linear factors with all coeff 1 of W-infinity.
AllOne := proc(sys, var, par, N)
local lis, ran, de, i, j, k, S, a, m, r, clin, cdlist;
lis, ran := getlis(sys, var, par, N);  
de       := [op({op(denom(lis))})]; 
for i from 1 to nops(de) do
    S||i := [];
    for j from 1 to nops(lis) do
        if denom(lis[j])=de[i] then
           S||i := [op(S||i), lis[j]];
        end if;
    end do;
end do;
clin := [];
for i from 1 to nops(de) do
    a := de[i];
    for k from a by a to trunc(nops(par)/a)*a do
        if k<>1 then
           if nops(S||i)>0 then
              m, r := binar(k, ran, par, k*S||i);
              clin := [op(clin), op(m)];
              S||i := r/k;                
           else
              break;
           end if;
        end if;
    end do;
end do;
cdlist := [seq(0, i=1..nops(par))];
for i from 1 to nops(par) do
    cdlist[i] := cdlist[i]+add(degree(clin[j], par[i]), j=1..nops(clin));
end do;
return clin, cdlist;
end proc:

##################
AllTerm := proc(d, dlist, par)
local T, i, k, c, B, t; 
T := Array(1..(d+1)^nops(dlist));
if nops(dlist)=2 then  
   c := 1;     
   for i from 0 to dlist[1] do
       for k from 0 to dlist[2] do
           if i+k=d then T[c] := par[1]^i*par[2]^k; c := c+1; end if;
       end do;
   end do;
   return T;
else 
   c := 1; 
   for k from 0 to d do
       for i from 0 to dlist[1] do
           if i+k = d then
              B := AllTerm(k, dlist[2..-1], par[2..-1]);
              for t from 1 to ArrayNumElems(B, NonZero) do
                  T[c] := par[1]^i*B[t];
                  c    := c+1;
              end do;
           end if; 
       end do;            
   end do;
   return T;
end if;
end proc:

##################
Sample_notallone := proc(sys, var, par, key, td, lin, N, N_change)
local R, R_change, A, ssys, rlin, lis, notallone_factors, K_change, i;
global count;
R        := rand(1..N);
R_change := rand(1..N_change); 
A        := [seq(R(), i = 1 .. nops(par), 2), seq(R_change(), i = 1 .. nops(par), 2)];
ssys     := subs(seq(par[i]=A[i], i=1..(key-1)), seq(par[i]=A[i], i=(key+1)..nops(par)), sys);
rlin     := subs(seq(par[i]=A[i], i=1..(key-1)), seq(par[i]=A[i], i=(key+1)..nops(par)), lin);
rlin     := [seq(rlin[i]/lcoeff(rlin[i]), i=1..nops(rlin))];
A        := subsop(key=NULL, A);
lis      := wif(ssys, var, [par[key]]);
count    := count + 1;
notallone_factors := [];
for i from 1 to nops(lis) do
    if degree(lis[i])=1 and evalb(lis[i] in rlin)=false then
        notallone_factors := [op(notallone_factors), lis[i]];
    end if;
end do;
while nops(notallone_factors)<>td do
      K_change    := N_change + 10;
      notallone_factors, A := Sample_notallone(sys, var, par, key, td, lin, N, K_change);    
end do;
return notallone_factors, A;
end proc: 

##################
Sample_nonlinear := proc(sys, var, par, key, nd, N, N_change)
local R, R_change, A, ssys, lis, nonlinear, K_change, i;
global count;
R        := rand(1..N);
R_change := rand(1..N_change); 
A        := [seq(R(), i = 1 .. nops(par), 2), seq(R_change(), i = 1 .. nops(par), 2)];
ssys     := subs(seq(par[i]=A[i], i=1..(key-1)), seq(par[i]=A[i], i=(key+1)..nops(par)), sys);
A        := subsop(key=NULL, A);
lis      := wif(ssys, var, [par[key]]);
count    := count + 1;
nonlinear := 1;
for i from 1 to nops(lis) do
    if degree(lis[i])>1 then
        nonlinear := nonlinear * lis[i];
    end if;
end do;
while nops(nonlinear)<>(nd+1) do
      K_change     := N_change + 10;
      nonlinear, A := Sample_nonlinear(sys, var, par, key, nd, N, K_change);    
end do;
return nonlinear, A;
end proc: 

##################
Sample_both := proc(sys, var, par, key, nd, td, lin, N, N_change)
local R, R_change, A, ssys, rlin, lis, nonlinear_factors, notallone_factors, K_change, i, nonlinear;
global count;
R        := rand(1..N);
R_change := rand(1..N_change); 
A        := [seq(R(), i = 1 .. nops(par), 2), seq(R_change(), i = 1 .. nops(par), 2)];
ssys     := subs(seq(par[i]=A[i], i=1..(key-1)), seq(par[i]=A[i], i=(key+1)..nops(par)), sys);
rlin     := subs(seq(par[i]=A[i], i=1..(key-1)), seq(par[i]=A[i], i=(key+1)..nops(par)), lin);
rlin     := [seq(rlin[i]/lcoeff(rlin[i]), i=1..nops(rlin))];
A        := subsop(key=NULL, A);
lis      := wif(ssys, var, [par[key]]);
count    := count + 1;
nonlinear         := 1;
notallone_factors := [];
for i from 1 to nops(lis) do
    if degree(lis[i])>1 then
         nonlinear := nonlinear * lis[i];
    elif degree(lis[i])=1 and evalb(lis[i] in rlin)=false then
         notallone_factors := [op(notallone_factors), lis[i]];
    end if;
end do;
while nops(nonlinear)<>(nd+1) or nops(notallone_factors)<>td do
      K_change    := N_change + 10;
      nonlinear, notallone_factors, A := Sample_both(sys, var, par, key, nd, td, lin, N, K_change);    
end do;
return nonlinear, notallone_factors, A;
end proc: 

################## The function is to compute nonlinear factors of W-infinity.
Nonlinear := proc(sor, newsys, newvar, par, key, nondlist, newlin, td, N)
local d, restpar, restd, T, M, i, j, k, temp, inters, S, non, nlin, A, DJ, m, B, C, mon, v, non_list, non_poly, notallone_list, notallone_poly;
d       := nondlist[key]; 
restpar := subsop(key=NULL, par);
restd   := subsop(key=NULL, nondlist);
T       := Array(1..d, 1..(d+1)^nops(restpar));
M       := 1;
for i from 1 to d do
     temp := AllTerm(i, restd, restpar);
     M    := max(M, ArrayNumElems(temp, NonZero));
     for j from 1 to ArrayNumElems(temp, NonZero) do
         T[i, j] := temp[j];
     end do; 
end do;
S      := Array(1..M);
inters := Array(1..M);
if sor = 1 then
    for i from 1 to M do
        S[i]        := [Sample_nonlinear(newsys, newvar, par, key, d, N, N)];
    end do;
else   
    for i from 1 to M do
        non_poly, notallone_list, A := Sample_both(newsys, newvar, par, key, d, td, newlin, N, N);
        notallone_poly              := expand(mul(notallone_list[i], i=1..nops(notallone_list)));
        S[i]                        := [non_poly,  A];
        inters[i]                   := [notallone_poly, A];
    end do;
end if;
DJ := par[key]^d;
for i from 1 to d do
    m := ArrayNumElems(T[i], NonZero);
    if i<>d then 
       B := [seq(coeff(S[k][1], par[key]^(d-i)), k=1..m)];
    else
       B := [seq(subs(par[key]=0, S[k][1]), k=1..m)];
    end if;
    C := Array(1..m, 1..m);
    for j from 1 to m do
        C[j] := subs(seq(restpar[k]=S[j][2][k], k=1..nops(restpar)), T[i][1..m]);
    end do;
    mon := Matrix([T[i][1..m]]).MatrixInverse(Matrix(C)).Transpose(Matrix([B]));
    DJ  := DJ + mon[1, 1] * par[key]^(d-i);       
end do;
# save S, inters, DJ, "bc6_nonlinear.txt";
return DJ, inters;
end proc: 

################## Initial step=1.
rectree := proc(lis, num, step)    
local le, A, ls, R, r, newrow, newcol, i, j, k, t, s;
if step=nops(lis) then
   le := choose(num, lis[step]);
   A  := Array(1..nops(le), 1..1);
   for i from 1 to nops(le) do
       A[i, 1] := le[i];
   end do;
   return A;
end if;
if step<nops(lis) then
   ls     := choose(num, lis[step]); 
   R      := rectree(lis, num, step+1);
   r      := [upperbound(R)]; 
   newrow := r[1]*nops(ls); 
   newcol := r[2]+1; 
   A      := Array(1..newrow, 1..newcol); 
   for i from 1 by r[1] to newrow-r[1]+1 do
       for j from i to i+r[1]-1 do
           s       := iquo(j-1, r[1])+1;
           A[j, 1] := ls[s];
           for k from 2 to newcol do
               t := modp(j, r[1]);
               if t=0 then t := r[1]; end if;
               A[j, k] := R[t, k-1];
           end do;      
       end do;
   end do;
   return A;
end if;
end proc:

##################
maintree := proc(par, lis, num, key)
local newlis, newpar, i, j, k, A, r, R, E, q, li, D, a, b, nt, F, J, new, temp, d, ter, g;
newlis := lis;
newpar := par;
for i from 1 to nops(par) do
    if lis[i]=0 then
       newlis := subsop(i = NULL, lis);
       newpar := subsop(i = NULL, par);
    end if;
end do;
A := rectree(newlis, num, 1);
r := [upperbound(A)];
R := Array(1..r[1], 1..num);
E := Array(1..r[1], 1..num);
q := 1;
for i from 1 to r[1] do
    li := [];
    for j from 1 to num do
        for k from 1 to nops(newpar) do
            if evalb(j in A[i, k])=true then
               R[i, j] := R[i, j]+par[k];
            end if;
        end do;
        li := [op(li), nops(R[i, j])];
    end do;
    if evalb(1 in li)=false then
       E[q] := R[i];
          q := q + 1;
    end if;
end do;
q := q - 1;
D := Array(1..q, 1..num, fill=[1, 1]);
for i from 1 to q do
    D[i, 1] := [E[i, 1], 1];
    a       := 1;
    for j from 2 to num do
        b := 1;
        for k from 1 to a do
            if E[i, j]=D[i, k][1] then
               D[i, k][2] := D[i, k][2] + 1;
               b          := b + 1;
               break;
            end if;
        end do;  
        if b=1 then
               D[i, a+1]  := [E[i, j], 1];
               a          := a+1;
        end if; 
    end do;
    T||i := {seq(D[i, j], j=1..num)}; 
end do;
F   := {seq(T||i, i=1..q)};
d   := nops(F);
new := Array(1..d, 1..num);
ter := Array(1..d, 1..num, fill=[]);
nt  := Array(1..d, 1..num);
for i from 1 to d do
    temp := op(i, F);
    for j from 1 to nops(temp) do
        new[i, j] := op(j, temp);
    end do;  
    f||i  := expand(mul(new[i, j][1]^new[i,j][2], j=1..ArrayNumElems(new[i], NonZero)));
    for j from 1 to num do
        g := coeff(f||i, par[key], num-j);
        for k from 1 to nops(g) do
            ter[i, j] := [op(ter[i, j]), op(k, g)/lcoeff(op(k, g))]; 
        end do;
        nt[i, j] := nops(ter[i, j]);
    end do;  
end do; 
return ter, nt;
end proc:

##################
NotAllOne := proc(newsys, var, par, key, ndlist, newlin, inters, N)
local restpar, num, ter, nt, nrow, DJ, T, temp, S, SS, B, C, mon, uterm, m, M, cterm, ncterm, cand, q, fDJ, mDJ, v, i, j, k, numin, notallone_list, notallone_poly, A;
restpar := subsop(key=NULL, par);
num     := ndlist[key];
ter, nt := maintree(par, ndlist, num, key);
nrow    := upperbound(ter, 1); 
DJ      := par[key]^num;
T       := Array(1..num, 1..max(nt));
###### = 1 possibility
if nrow=1 then
   for i from 1 to num do
       temp := ter[1, i];
       for j from 1 to nops(temp) do
           T[i, j] := temp[j];
       end do; 
   end do;
   M := max(nt);
   S := Array(1..M);
   if type(inters, 'list') then
       for i from 1 to M do 
           notallone_list, A := Sample_notallone(newsys, var, par, key, num, newlin, N, N);
           notallone_poly    := expand(mul(notallone_list[i], i=1..nops(notallone_list)));
           S[i] := [notallone_poly, A]; 
        end do;
   else  
       numin := ArrayNumElems(inters);
       if M<=numin then
           for i from 1 to M do S[i] := inters[i]; end do;
       else
           for i from 1 to numin do   S[i] := inters[i]; end do;
           for i from numin+1 to M do 
               notallone_list, A := Sample_notallone(newsys, var, par, key, num, newlin, N, N);
               notallone_poly    := expand(mul(notallone_list[i], i=1..nops(notallone_list)));
               S[i] := [notallone_poly, A]; 
            end do;
       end if;
   end if;
   for i from 1 to num do
       m := ArrayNumElems(T[i], NonZero);
       if i<>num then 
          B := [seq(coeff(S[k][1], par[key]^(num-i)), k=1..m)];
       else
          B := [seq(subs(par[key]=0, S[k][1]), k=1..m)];
       end if;
       C := Array(1..m, 1..m);
       for j from 1 to m do
           C[j] := subs(seq(restpar[k]=S[j][2][k], k=1..nops(restpar)), T[i][1..m]);
       end do;
       mon := Matrix([T[i][1..m]]).MatrixInverse(Matrix(C)).Transpose(Matrix([B]));
       DJ  := DJ + mon[1, 1]*par[key]^(num-i);        
   end do;
###### >1 possibilities
else
   uterm := Array(1..num-1, fill={});
   for i from 1 to num-1 do
       for j from 1 to nrow do
           uterm[i] := uterm[i] union {op(ter[j, i])};
       end do;
       for j from 1 to nops(uterm[i]) do
           T[i, j] := op(j, uterm[i]);
       end do; 
   end do;
   M := max(seq(nops(uterm[i]), i=1..num-1)); 
   S := Array(1..M);
   ###### DJ = v0^{num} + C_{num-1} * v0^{num-1} + ... + C_{1} * v0^{1} + C_{0}
   ###### Interpolate for C_{num-1},...,C_{1} 
   if type(inters, 'list') then
       for i from 1 to M do 
           notallone_list, A := Sample_notallone(newsys, var, par, key, num, newlin, N, N);
           notallone_poly    := expand(mul(notallone_list[i], i=1..nops(notallone_list)));
           S[i] := [notallone_poly, A]; 
        end do;
   else  
       numin := ArrayNumElems(inters); 
       if M<=numin then
           for i from 1 to M do S[i] := inters[i]; end do;
       else
           for i from 1 to numin do   S[i] := inters[i]; end do;
           for i from numin+1 to M do 
               notallone_list, A := Sample_notallone(newsys, var, par, key, num, newlin, N, N);
               notallone_poly    := expand(mul(notallone_list[i], i=1..nops(notallone_list)));
               S[i] := [notallone_poly, A];  
            end do;
       end if;
   end if;
   ###### Solve the linear system for C_{num-1},...,C_{1} 
   cterm := Array(1..num-1, fill={});
   for i from 1 to num-1 do
       m   := ArrayNumElems(T[i], NonZero);
       B   := [seq(coeff(S[k][1], par[key]^(num-i)), k=1..m)];
       C   := Array(1..m, 1..m);
       for j from 1 to m do
           C[j] := subs(seq(restpar[k]=S[j][2][k], k=1..nops(restpar)), T[i][1..m]);
       end do;
       mon := Matrix([T[i][1..m]]).MatrixInverse(Matrix(C)).Transpose(Matrix([B]));
       for j from 1 to nops(mon[1, 1]) do
           temp     := op(j, mon[1, 1]); 
           cterm[i] := cterm[i] union {temp/lcoeff(temp)};
       end do;
       DJ  := DJ + mon[1, 1]*par[key]^(num-i);    
   end do;
   ncterm := [seq(nops(cterm[i]), i=1..num-1)];
   cand   := [];
   for j from 1 to nrow do
       temp := [seq(nt[j, i], i=1..num-1)];
       if evalb(temp=ncterm)=true then
          q := 0;
          for i from 1 to num-1 do
              if nt[j, i]=nops(uterm[i]) or {op(ter[j, i])}=cterm[i] then q := q+1; end if;
          end do; 
          if q=num-1 then cand := [op(cand), [nt[j, num], j]]; end if;
       end if;
   end do;
   cand := sort(cand, (x, y) -> y[1] <= x[1]); 
   for i from 1 to nops(cand) do
       temp := ter[cand[i][2], num]; 
       m    := nops(temp);  
       ###### Interpolate for C_{0} 
       if i=1 then
           SS := Array(1..m);
           if type(inters, 'list') then                            
               if m<=M then for j from 1 to m do SS[j] := S[j]; end do;
               else
                   for j from 1 to M do   SS[j] := S[j]; end do;
                   for j from M+1 to m do 
                       notallone_list, A := Sample_notallone(newsys, var, par, key, num, newlin, N, N);
                       notallone_poly    := expand(mul(notallone_list[i], i=1..nops(notallone_list))); 
                       SS[j] := [notallone_poly, A]; 
                    end do;
               end if;
           else
               if m<=M then for j from 1 to m do SS[j] := S[j]; end do;
               elif max(m, M, numin)=numin then for j from 1 to m do SS[j] := inters[j]; end do;
               elif min(m, M, numin)=M then
                    for j from 1 to numin do SS[j] := inters[j]; end do;
                    for j from numin+1 to m do 
                        notallone_list, A := Sample_notallone(newsys, var, par, key, num, newlin, N, N);
                        notallone_poly    := expand(mul(notallone_list[i], i=1..nops(notallone_list))); 
                        SS[j] := [notallone_poly, A]; 
                    end do;
               elif min(m, M, numin)=numin then
                    for j from 1 to M do SS[j] := S[j]; end do;
                    for j from M+1 to m do 
                        notallone_list, A := Sample_notallone(newsys, var, par, key, num, newlin, N, N);
                        notallone_poly := expand(mul(notallone_list[i], i=1..nops(notallone_list)));       
                        SS[j] := [notallone_poly, A]; 
                    end do;
               end if;
           end if;
       end if;
       ###### Solve the linear system for C_{0}.
       for j from 1 to m do T[num, j] := temp[j]; end do; 
       B := [seq(subs(par[key]=0, SS[k][1]), k=1..m)]; 
       C := Array(1..m, 1..m);
       for j from 1 to m do
           C[j] := subs(seq(restpar[k]=SS[j][2][k], k=1..nops(restpar)), T[num][1..m]);
       end do;
       mon := Matrix([T[num][1..m]]).MatrixInverse(Matrix(C)).Transpose(Matrix([B]));
       DJ  := DJ + mon[1, 1]; 
       fDJ := factors(DJ); 
       if nops(fDJ[2])=num then 
          break; 
        end if;
   end do;
end if;
return DJ;
end proc:

##################
ww := proc(f, var, par, N_linear, N_cone, N)
### LinearOperator: N_linear
### AllOne        : N_cone
### Interpolate   : N
local sys, newvar, clin, cdlist, newsys, tt, newdlist, nondlist, key, newpar, newlin, ndlist, non, nlin, l, i, inters, factorl, v, newl, NN_linear, NN_cone, NN;
global count;
count        := 0;
sys, newvar  := lle(f, var, par);
newsys, tt, newdlist, nondlist, key, newpar := LinearOperator(sys, newvar, par, N_linear); 
st  := time():
clin, cdlist := AllOne(sys, newvar, par, N_cone);
cdlist[key]  := nops(clin); 
ndlist := [seq(newdlist[i]-nondlist[i]-cdlist[i], i=1..nops(newdlist))];
if max(nondlist)=0 and max(ndlist)=0 then
     l := mul(clin[i], i=1..nops(clin));
     return l;
elif max(nondlist)>0 and max(ndlist)=0 then
     newl, inters := Nonlinear(1, newsys, newvar, par, key, nondlist, [], ndlist[key], N);
elif max(nondlist)=0 and max(ndlist)>0 then
     newlin       := subs(seq(par[i]=newpar[i], i=1..nops(par)), clin);
     newl         := NotAllOne(newsys, newvar, par, key, ndlist, newlin, [], N); 
else 
     newlin       := subs(seq(par[i]=newpar[i], i=1..nops(par)), clin);
     non, inters  := Nonlinear(2, newsys, newvar, par, key, nondlist, newlin, ndlist[key], N); 
     nlin         := NotAllOne(newsys, newvar, par, key, ndlist, newlin, inters, N); 
     newl         := non * nlin;
end if;
v := solve([seq(t||i-newpar[i], i=1..nops(par))], par);
l := subs([seq(t||i=par[i], i=1..nops(par))], subs(op(v), newl));
l := expand(l * mul(clin[i], i=1..nops(clin)));
l := l/lcoeff(l, order = tdeg(op(par)));
l := factor(l);
st1       := time()-st;
save st1, l, "bc9.mpl";
return l, count;
end proc: