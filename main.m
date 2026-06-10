g := StringToInteger(g);          // genus
n := 2*g-1;
p := StringToInteger(p);          // characteristic
e := Integers()!((p-1)/2);

K := GF(p^2);
R<x> := PolynomialRing(K);
S := [];
for a in K do
    if a ne 0 and a ne 1 then
        if IsSquare(a) and IsSquare(1-a) then
            Append(~S,a);
        end if;
    end if;
end for;

function is_compatible(a,current_set)
    for b in current_set do
        if not IsSquare(a-b) then
            return false;
        end if;
    end for;
    return true;
end function;

function rosenhain_invariants(lambda_set)
    branch_points := lambda_set join {0,1};
    orbit := {};
    for triple in Permutations(branch_points,3) do  // (a1,a2,a3) -> (0,1,inf)
        a1,a2,a3 := Explode(triple); c := (a2-a3)/(a2-a1);
        inv := {c};
        for a in branch_points diff SequenceToSet(triple) do
            Include(~inv,c*(a-a1)/(a-a3));
        end for;
        Include(~orbit,inv);
    end for;
    for pair in Permutations(branch_points,2) do   // (a1,a2,inf) -> (0,1,inf)
        a1,a2 := Explode(pair); c := 1/(a2-a1);
        inv := {};
        for a in branch_points diff SequenceToSet(pair) do
            Include(~inv,c*(a-a1));
        end for;
        Include(~orbit,inv);
    end for;
    for pair in Permutations(branch_points,2) do   // (a1,inf,a3) -> (0,1,inf)
        a1,a3 := Explode(pair);
        inv := {};
        for a in branch_points diff SequenceToSet(pair) do
            Include(~inv,(a-a1)/(a-a3));
        end for;
        Include(~orbit,inv);
    end for;
    for pair in Permutations(branch_points,2) do   // (inf,a2,a3) -> (0,1,inf)
        a2,a3 := Explode(pair); c := a2-a3;
        inv := {};
        for a in branch_points diff SequenceToSet(pair) do
            Include(~inv,c/(a-a3));
        end for;
        Include(~orbit,inv);
    end for;
    return orbit;
end function;

function is_superspecial(f)
    F := f^e;
    for i,j in [1..g] do
        if Coefficient(F,i*p-j) ne 0 then
            return false;
        end if;
    end for;
    return true;
end function;

procedure search_lambdas(start_index,current_set,~candidates,~track_table)
    if #current_set eq n then
        lambda_set := SequenceToSet(current_set);
        if not IsDefined(track_table,lambda_set) then
            Append(~candidates,current_set);
            for inv in rosenhain_invariants(lambda_set) do
                track_table[inv] := true;
            end for;
        end if;
        return;
    end if;
    if (#S-start_index+1) lt (n-#current_set) then
        return;
    end if;
    for k in [start_index..#S] do
        a := S[k];
        if is_compatible(a,current_set) then
            next_set := Append(current_set,a);
            search_lambdas(k+1,next_set,~candidates,~track_table);
        end if;
    end for;
end procedure;

candidates := [];
track_table := AssociativeArray();
search_lambdas(1,[],~candidates,~track_table);
printf "In characteristic p = %o.\n", p;
ssp_hyps := [];
for lambda_set in candidates do
    f := x*(x-1)*&*[x-a: a in lambda_set];
    if is_superspecial(f) then
        Append(~ssp_hyps,f);
    end if;
end for;
printf "There are %o superspecial hyperelliptic curves of genus %o as follows:\n", #ssp_hyps,g;
ssp_hyps;
quit;
