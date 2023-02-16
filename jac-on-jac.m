
// Author: Elif Ozbay Gurler, 2023.

clear;

__:=0;

swap:=function(P,Q,dP,dQ)
    return Q,P,dQ,dP;
end function;

getcoords:=function(D,deg)
    if deg eq 0 then
        return 1,__,0,__,0,1,0;
    elif deg eq 1 then
        return D[1],__,D[2],__,D[3],D[4],1;
    else
        return D[1],D[2],D[3],D[4],D[5],D[6],2;
    end if;
end function;

printCoords:=procedure(P,dPP,Q,dQQ,R)
    x:=R.1;
    "P";
    if dPP eq 0 then
        "[1,0]";
    elif dPP eq 1 then
        x1:=-Coefficient(P[1],0);
        y1:=Coefficient(P[2],0);
        "x1,y1",[x1,y1];
    elif dPP eq 2 then
        q1:=Coefficient(P[1],1);
        r1:=Coefficient(P[1],0);
        s1:=Coefficient(P[2],1);
        t1:=Coefficient(P[2],0);
        ff1:=Factorization(x^2+q1*x+r1);
        if ff1[1][1] eq x^2+q1*x+r1 then
            "Roots in extension";
        else
            if #ff1 eq 1 then
                x1:=-Coefficient(ff1[1][1],0);
                x2:=x1;
            else
                x1:=-Coefficient(ff1[1][1],0);
                x2:=-Coefficient(ff1[2][1],0);
            end if;
            y1:=s1*x1+t1; y2:=s1*x2+t1;
            "x1,y1",[x1,y1];
            "x2,y2",[x2,y2];
        end if;
    end if;
    "Q";
    if dQQ eq 0 then
        "[1,0]";
    elif dQQ eq 1 then
        x2:=-Coefficient(Q[1],0);
        y2:=Coefficient(Q[2],0);
        "x2,y2",[x2,y2];
    elif dQQ eq 2 then
        q2:=Coefficient(Q[1],1);
        r2:=Coefficient(Q[1],0);
        s2:=Coefficient(Q[2],1);
        t2:=Coefficient(Q[2],0);
        ff2:=Factorization(x^2+q2*x+r2);
        if ff2[1][1] eq x^2+q2*x+r2 then
            "Roots in extension";
        else
            if #ff2 eq 1 then
                x3:=-Coefficient(ff2[1][1],0);
                x4:=x3;
            else
                x3:=-Coefficient(ff2[1][1],0);
                x4:=-Coefficient(ff2[2][1],0);
            end if;
            y3:=s2*x3+t2; y4:=s2*x4+t2;
            "x3,y3",[x3,y3];
            "x4,y4",[x4,y4];
        end if;
    end if;
end procedure;

// ############# AFFINE FORMULAS #############

add11:=function(x1,y1,x2,y2,a3,a2,a1,a0)
    if x1 eq x2 and y1 eq -y2 then
        return 1,__,0,__,0,__,0;
    elif x1 eq x2 and y1 eq y2 then
        q3:=-2*x1; 
        r3:=x1^2;
        s3:=(5*x1^4+3*a3*x1^2+2*a2*x1+a1)/(2*y1);
        t3:=(-3*x1^5-a3*x1^3+a1*x1+2*a0)/(2*y1);
        return q3,r3,s3,t3,1,1,2;
    else
        q3:=-x1-x2;
        r3:=x1*x2;
        s3:=(y1-y2)/(x1-x2);
        t3:=(x1*y2-x2*y1)/(x1-x2);
        return q3,r3,s3,t3,1,1,2;
    end if;
end function;

add12trp:=function(x1,y1,a3,a2,a1)
    ffx1:=5*x1^4+3*a3*x1^2+2*a2*x1+a1;
    fffx1:=20*x1^3+6*a3*x1+2*a2;
    A:=(2*y1^2*fffx1-ffx1^2)/(8*y1^3);
    B:=ffx1/(2*y1)-2*A*x1;
    C:=y1-A*x1^2-B*x1;
    q3:=3*x1-A^2;
    r3:=a3-2*A*B+3*x1*(q3-x1);
    s3:=A*q3-B;
    t3:=A*r3-C;
    return q3,r3,s3,t3,1,1,2;
end function;

add12dbladd:=function(x1,y1,x4,y4,a3,a2,a1,a0)
    q,r,s,t:=add11(x1,y1,x1,y1,a3,a2,a1,a0);
    A:=(y4-s*x4-t)/(x4^2+q*x4+r);
    B:=s+q*A;
    C:=t+r*A;
    q3:=x4-q-A^2;
    r3:=a3+q^2-r-A*(B+s)+x4*q3;
    s3:=A*q3-B;
    t3:=A*r3-C;
    return q3,r3,s3,t3,1,1,2;
end function;

add12g:=function(x1,y1,q2,r2,s2,t2,a3)
    A:=(y1-s2*x1-t2)/(x1^2+q2*x1+r2);
    B:=s2+q2*A;
    C:=t2+r2*A;
    q3:=x1-q2-A^2;
    r3:=a3+q2^2-r2-A*(B+s2)+x1*q3;
    s3:=A*q3-B;
    t3:=A*r3-C;
    return q3,r3,s3,t3,1,1,2;
end function;

add12:=function(x1,y1,q2,r2,s2,t2,a3,a2,a1,a0)
    if x1^2+q2*x1+r2 eq 0 then
        x3:=x1;
        y3:=s2*x1+t2;
        x4:=-q2-x3;
        y4:=s2*x4+t2;
        if y1 eq -y3 then
            return x4,__,y4,__,1,1,1;
        elif y1 eq y3 then
            if x1 eq x4 then
                return add12trp(x1,y1,a3,a2,a1);
            else
                return add12dbladd(x1,y1,x4,y4,a3,a2,a1,a0);
            end if;
        end if;
    else
        return add12g(x1,y1,q2,r2,s2,t2,a3);
    end if;
end function;

dbl2b0:=function(q1,r1,s1,t1,a3,a2,a1,a0)
    x2:=-t1/s1;
    x1:=-q1-x2;
    y1:=s1*x1+t1;
    return add11(x1,y1,x1,y1,a3,a2,a1,a0);
end function;

dbl2:=function(q1,r1,s1,t1,B,a3,a2)
    A:=((q1^2-4*r1+a3)*q1-a2+s1^2)*(q1*s1-t1)+(3*q1^2-2*r1+a3)*r1*s1;
    C:=((q1^2-4*r1+a3)*q1-a2+s1^2)*s1+(3*q1^2-2*r1+a3)*t1;
    if C eq 0 then
        x5:=2*q1+A^2/B^2;
        y5:=(A/B*(q1+x5)-s1)*x5+A/B*r1-t1;
        return x5,__,y5,__,1,1,1;
    else
        q3:=2*A/C-B^2/C^2;
        r3:=A^2/C^2+2*q1*B^2/C^2-2*s1*(B/C);
        s3:=(r1-r3)*(C/B)-q3*(q1-q3)*(C/B)+(q1-q3)*(A/B)-s1;
        t3:=(r1-r3)*(A/B)-r3*(q1-q3)*(C/B)-t1;
        return q3,r3,s3,t3,1,1,2;
    end if;
end function;

add22ppmq:=function(q1,r1,s1,t1,q2,r2,s2,t2,a3,a2,a1,a0)
    x1:=(t1-t2)/(s2-s1);
    y1:=s1*x1+t1;
    return add11(x1,y1,x1,y1,a3,a2,a1,a0);
end function;

add22b0:=function(q1,r1,s1,t1,q2,r2,s2,t2,a3,a2,a1,a0)
    x1:=-(r1-r2)/(q1-q2);   y1:=s1*x1+t1;
    x3:=x1;                 y3:=s2*x3+t2;
    x2:=-q1-x1;             y2:=s1*x2+t1;
    x4:=-q2-x3;             y4:=s2*x4+t2;
    if y1 eq -y3 then
        return add11(x2,y2,x4,y4,a3,a2,a1,a0);
    else
        q,r,s,t,__,__,__:=add11(x1,y1,x1,y1,a3,a2,a1,a0);
        q,r,s,t,__,__,__:=add12(x2,y2,q,r,s,t,a3,a2,a1,a0);
        return add12(x4,y4,q,r,s,t,a3,a2,a1,a0);
    end if;
end function;

add22:=function(q1,r1,s1,t1,q2,r2,s2,t2,B)
    A:=(t1-t2)*(q2*(q1-q2)-(r1-r2))-r2*(q1-q2)*(s1-s2);
    C:=(q1-q2)*(t1-t2)-(r1-r2)*(s1-s2);
    if C eq 0 then
        x5:=(q1+q2)+A^2/B^2;
        y5:=(A/B*(q1+x5)-s1)*x5+A/B*r1-t1;
        return x5,__,y5,__,1,1,1;
    else
        q3:=(q1-q2)+2*(A/C)-B^2/C^2;
        r3:=(q1-q2)*(A/C)+A^2/C^2+(q1+q2)*B^2/C^2-(s1+s2)*(B/C);
        s3:=(r1-r3)*(C/B)-q3*(q1-q3)*(C/B)+(q1-q3)*(A/B)-s1;
        t3:=(r1-r3)*(A/B)-r3*(q1-q3)*(C/B)-t1;
        return q3,r3,s3,t3,1,1,2;
    end if;
end function;

addDivisor:=function(P,dP,Q,dQ,a3,a2,a1,a0)
	if dP eq 0 then
        return getcoords(Q,dQ);
    elif dQ eq 0 then
        return getcoords(P,dP);
    elif dP eq 1 and dQ eq 1 then
        x1,__,y1,__,__:=getcoords(P,dP);
        x2,__,y2,__,__:=getcoords(Q,dQ);
        return add11(x1,y1,x2,y2,a3,a2,a1,a0);
    elif dP+dQ eq 3 then
        if dP eq 2 then
            P,Q,dP,dQ:=swap(P,Q,dP,dQ);
        end if;
        x1,__,y1,__,__:=getcoords(P,dP);
        q2,r2,s2,t2,__:=getcoords(Q,dQ);
        return add12(x1,y1,q2,r2,s2,t2,a3,a2,a1,a0);
    elif dP eq 2 and dQ eq 2 then
        q1,r1,s1,t1,__:=getcoords(P,dP);
        q2,r2,s2,t2,__:=getcoords(Q,dQ);
        if q1 eq q2 and r1 eq r2 then
            if s1 eq -s2 and t1 eq -t2 then
                return 1,__,0,__,0,1,1;
            elif s1 eq s2 and t1 eq t2 then
                B:=2*(q1*s1-t1)*t1-2*r1*s1^2;
                if B eq 0 then
                    return dbl2b0(q1,r1,s1,t1,a3,a2,a1,a0);
                else
                    return dbl2(q1,r1,s1,t1,B,a3,a2);
                end if;
            else
                return add22ppmq(q1,r1,s1,t1,q2,r2,s2,t2,a3,a2,a1,a0);
            end if;
        else
            B:=(r1-r2)*(q2*(q1-q2)-(r1-r2))-r2*(q1-q2)^2;
            if B eq 0 then
                return add22b0(q1,r1,s1,t1,q2,r2,s2,t2,a3,a2,a1,a0);
            else
                return add22(q1,r1,s1,t1,q2,r2,s2,t2,B);
            end if;
        end if;
    end if;
end function;

// ############# PROJECTIVE FORMULAS #############

ADD11DBL:=function(X1,Y1,Z1,W1,a3,a2,a1,a0)
    XX1:=X1^2; XXXX1:=XX1^2; XXXXX1:=XXXX1*X1; a3XX1:=a3*XX1;
    ZZ1:=Z1^2;
    ZZZZ1:=ZZ1^2;
    Q3:=-2*X1;
    R3:=XX1;
    S3:=(((a1*ZZ1+2*a2*X1)*ZZ1+3*a3XX1)*ZZZZ1+5*XXXX1)*W1;
    T3:=(((2*a0*ZZ1+a1*X1)*ZZZZ1-a3XX1*X1)*ZZZZ1-3*XXXXX1)*W1;
    Z3:=Z1;
    W3:=2*Y1;
    return Q3,R3,S3,T3,Z3,W3,2;
end function;

ADD11ADD:=function(X1,Y1,Z1,W1,X2,Y2,Z2,W2)
    ZZ1:=Z1^2; ZZZZZ1:=ZZ1^2*Z1;
    ZZ2:=Z2^2; ZZZZZ2:=ZZ2^2*Z2;
    X1ZZ2:=X1*ZZ2; X2ZZ1:=X2*ZZ1;
    Y1ZZZZZ2W2:=Y1*ZZZZZ2*W2; Y2ZZZZZ1W1:=Y2*ZZZZZ1*W1;
    Q3:=-X1ZZ2-X2ZZ1;
    R3:=X1ZZ2*X2ZZ1;
    S3:=Y1ZZZZZ2W2-Y2ZZZZZ1W1;
    T3:=X1ZZ2*Y2ZZZZZ1W1-X2ZZ1*Y1ZZZZZ2W2;
    Z3:=Z1*Z2;
    W3:=(X1ZZ2-X2ZZ1)*W1*W2;
    return Q3,R3,S3,T3,Z3,W3,2;
end function;

ADD11:=function(X1,Y1,Z1,W1,X2,Y2,Z2,W2,a3,a2,a1,a0)
    ZZ1:=Z1^2; ZZZ1:=ZZ1*Z1; ZZZZZ1:=ZZZ1*ZZ1;
    ZZ2:=Z2^2; ZZZ2:=ZZ2*Z2; ZZZZZ2:=ZZZ2*ZZ2;
    X1ZZ2:=X1*ZZ2; Y1ZZZZZ2W2:=Y1*ZZZZZ2*W2;
    X2ZZ1:=X2*ZZ1; Y2ZZZZZ1W1:=Y2*ZZZZZ1*W1;
    if X1ZZ2 eq X2ZZ1 and Y1ZZZZZ2W2 eq -Y2ZZZZZ1W1 then
        // "ADD110";
        return 1,__,0,__,0,1,0;
    elif X1ZZ2 eq X2ZZ1 and Y1ZZZZZ2W2 eq Y2ZZZZZ1W1 then
        // "ADD112DBL";
        return ADD11DBL(X1,Y1,Z1,W1,a3,a2,a1,a0);
    else
        // "ADD112ADD";
        return ADD11ADD(X1,Y1,Z1,W1,X2,Y2,Z2,W2);
    end if;
end function;

ADD12TRP:=function(X1,Y1,Z1,W1,a3,a2,a1)
    XX1:=X1^2; XXX1:=XX1*X1;
    ZZ1:=Z1^2; ZZZZ1:=ZZ1^2;
    t3X1:=3*X1; t3a3X1:=a3*t3X1; a2ZZ1:=a2*ZZ1;
    FFX1W1:=((X1*(2*a2ZZ1+t3a3X1)+a1*ZZZZ1)*ZZZZ1+5*XX1^2)*W1;
    FFFX1:=2*(a2ZZ1+t3a3X1)*ZZZZ1+20*XXX1;
    t2YY1:=2*Y1^2; t8YYY1:=4*t2YY1*Y1; tt8YYY1:=t8YYY1^2;
    A:=(FFFX1*t2YY1-FFX1W1^2)*W1; AX1:=A*X1; AW1:=A*W1;
    B:=2*(FFX1W1*t2YY1-AX1);
    C:=t8YYY1*Y1-(AX1+B)*X1*W1;
    Q3:=tt8YYY1*t3X1-A^2;
    R3:=tt8YYY1*(a3*ZZZZ1*tt8YYY1-2*A*B+t3X1*(Q3-X1*tt8YYY1));
    S3:=AW1*Q3-B*tt8YYY1*W1;
    T3:=AW1*R3-C*tt8YYY1^2;
    Z3:=t8YYY1*Z1;
    W3:=W1;
    return Q3,R3,S3,T3,Z3,W3,2;
end function;

ADD12DBLADD:=function(X1,Y1,Z1,W1,X4,Y4,Z4,W4,a3,a2,a1,a0)
    XX1:=X1^2; XXXX1:=XX1^2; XXXXX1:=XXXX1*X1; a3XX1:=a3*XX1;
    ZZ1:=Z1^2; ZZZZ1:=ZZ1^2;
    Q3:=-2*X1; R3:=XX1;
    S3:=(((a1*ZZ1+2*a2*X1)*ZZ1+3*a3XX1)*ZZZZ1+5*XXXX1)*W1;
    T3:=(((2*a0*ZZ1+a1*X1)*ZZZZ1-a3XX1*X1)*ZZZZ1-3*XXXXX1)*W1;
    Z3:=Z1; W3:=2*Y1;
    ZZ3:=ZZ1; ZZ4:=Z4^2; ZZZZ4:=ZZ4^2;
    X4ZZ3:=X4*ZZ3; Y4ZZZZZ3:=Y4*ZZ3^2*Z3;
    Q3ZZ4:=Q3*ZZ4; R3ZZZZ4:=R3*ZZZZ4;
    S3ZZZ4:=S3*ZZ4*Z4; T3ZZZZZ4:=T3*ZZZZ4*Z4;
    W3W4:=W3*W4; WW3WW4:=W3W4^2; Z3Z4:=Z3*Z4; 
    K:=X4ZZ3*(Q3ZZ4+X4ZZ3)+R3ZZZZ4;
    KW3W4:=K*W3W4; KKWW3WW4:=KW3W4^2;
    KZ4:=K*Z4; KZ4W4:=KZ4*W4; S3KZ4W4:=S3*KZ4W4;
    A:=Y4ZZZZZ3*W3-(X4ZZ3*S3ZZZ4+T3ZZZZZ4)*W4;
    B:=S3KZ4W4+A*Q3;
    C:=T3*KZ4W4+A*R3;
    Q5:=(X4ZZ3-Q3ZZ4)*KKWW3WW4-A^2;
    R5:=((a3*Z3Z4^4+Q3ZZ4^2-R3ZZZZ4)*KKWW3WW4-A*ZZ4*(B+S3KZ4W4)+X4ZZ3*Q5)*KKWW3WW4;
    S5:=A*Q5-B*KZ4^2*WW3WW4;
    T5:=A*R5-C*KZ4^4*WW3WW4^2;
    Z5:=KW3W4*Z3Z4;
    W5:=1;
    return Q5,R5,S5,T5,Z5,W5,2;
end function;

ADD12G:=function(X1,Y1,Z1,W1,Q2,R2,S2,T2,Z2,W2,a3)
    ZZ1:=Z1^2; ZZZZ1:=ZZ1^2;
    ZZ2:=Z2^2; ZZZZZ2:=ZZ2^2*Z2;
    X1ZZ2:=X1*ZZ2; Q2ZZ1:=Q2*ZZ1; R2ZZZZ1:=R2*ZZZZ1;
    K:=X1ZZ2*(Q2ZZ1+X1ZZ2)+R2ZZZZ1; Z1Z2:=Z1*Z2;
    KZ1W1:=K*Z1*W1; KW2W1:=K*W2*W1; ZZZ1:=ZZ1*Z1;
    KK1WW2WW1:=KW2W1^2; KK1WW2WW1ZZ1:=KK1WW2WW1*ZZ1;
    S2KZ1W1:=S2*KZ1W1; T2KZ1W1:=T2*KZ1W1;
    A:=Y1*ZZZZZ2*W2-(S2*X1ZZ2+T2*ZZ1)*ZZZ1*W1;
    B:=S2KZ1W1+A*Q2;
    C:=T2KZ1W1+A*R2;
    Q3:=-(Q2ZZ1-X1ZZ2)*KK1WW2WW1-A^2;
    R3:=((a3*Z1Z2^4+Q2ZZ1^2-R2ZZZZ1)*KK1WW2WW1-A*ZZ1*(S2KZ1W1+B)+Q3*X1ZZ2)*KK1WW2WW1;
    S3:=A*Q3-B*KK1WW2WW1ZZ1;
    T3:=A*R3-C*KK1WW2WW1ZZ1^2;
    Z3:=KW2W1*Z1Z2;
    W3:=1;
    return Q3,R3,S3,T3,Z3,W3,2;
end function;

ADD12:=function(X1,Y1,Z1,W1,Q2,R2,S2,T2,Z2,W2,a3,a2,a1,a0)
    ZZ1:=Z1^2; ZZZZ1:=ZZ1^2; ZZ2:=Z2^2; ZZZZ2:=ZZ2^2; ZZZZZ2:=ZZZZ2*Z2;
    X1ZZ2:=X1*ZZ2; Q2ZZ1:=Q2*ZZ1; R2ZZZZ1:=R2*ZZZZ1;
    S2ZZZ1:=S2*ZZ1*Z1; T2ZZZZZ1:=T2*ZZZZ1*Z1;
    Q2pX1:=Q2ZZ1+X1ZZ2; Z1Z2:=Z1*Z2;
    K:=X1ZZ2*Q2pX1+R2ZZZZ1;
    if K eq 0 then
        X3:=X1; Y3:=S2ZZZ1*X1ZZ2+T2ZZZZZ1; Z3:=Z1; W3:=ZZZZZ2*W2;
        X4:=-Q2pX1; Y4:=S2ZZZ1*X4+T2ZZZZZ1; Z4:=Z1Z2; W4:=W2;
        Y1W3:=Y1*W3; Y3W1:=Y3*W1;
        if Y1W3 eq -Y3W1 then
            // "ADD121";
            return X4,__,Y4,__,Z4,W4,1;
        elif Y1W3 eq Y3W1 then
            if X1ZZ2 eq X4 then
                // "ADD12TRP";
                return ADD12TRP(X1,Y1,Z1,W1,a3,a2,a1);
            else
                // "ADD12DBLADD";
                return ADD12DBLADD(X1,Y1,Z1,W1,X4,Y4,Z4,W4,a3,a2,a1,a0);
            end if;
        end if;
    else
        // "ADD12G";
        return ADD12G(X1,Y1,Z1,W1,Q2,R2,S2,T2,Z2,W2,a3);
    end if;
end function;

DBL2B0:=function(Q1,R1,S1,T1,Z1,W1,a3,a2,a1,a0)
    X2:=-T1; XP1:=-(Q1*S1+X2)*S1; YP1:=(S1*T1+XP1)*S1^4; ZP1:=S1*Z1; WP1:=W1;
    XXP1:=XP1^2; XXXXP1:=XXP1^2; XXXXXP1:=XXXXP1*XP1; a3XXP1:=a3*XXP1;
    ZZP1:=ZP1^2; ZZZZP1:=ZZP1^2;
    Q3:=-2*XP1; R3:=XXP1;
    S3:=(((a1*ZZP1+2*a2*XP1)*ZZP1+3*a3XXP1)*ZZZZP1+5*XXXXP1)*WP1;
    T3:=(((2*a0*ZZP1+a1*XP1)*ZZZZP1-a3XXP1*XP1)*ZZZZP1-3*XXXXXP1)*WP1;
    Z3:=ZP1; W3:=2*YP1;
    return Q3,R3,S3,T3,Z3,W3,2;
end function;

DBL2C0:=function(Q1,R1,S1,T1,Z1,W1,A,B,a3,a2)
    BW1:=B*W1; BB2WW1:=BW1^2; Q1BB2WW1:=Q1*BB2WW1;
    X3:=2*Q1BB2WW1+A^2;
    Y3:=(A*(Q1BB2WW1+X3)-B*S1*BB2WW1)*X3+(A*R1-B*T1)*BB2WW1^2;
    Z3:=Z1*BW1;
    W3:=1;
    return X3,__,Y3,__,Z3,W3,1;
end function;

DBL2G:=function(Q1,R1,S1,T1,Z1,W1,A,B,C,a3,a2)
    CC:=C^2; CCCC:=CC^2; CCC:=C*CC; CCCB:=CCC*B;
    NQ1:=Q1*CC; NR1:=R1*CCCC; NS1:=S1*CCCB; NT1:=T1*CC*CCCB; Z3:=Z1*C;
    W3:=W1*B; WW3:=W3^2; D:=A*C; E:=D-WW3; Q3:=D+E; R3:=D^2-2*(NS1-NQ1*WW3);
    F:=NQ1-Q3; G:=NR1-R3; S3:=G-E*F-NS1; T3:=G*D-R3*F-NT1;
    return Q3,R3,S3,T3,Z3,W3,2;
end function;

DBL2:=function(Q1,R1,S1,T1,Z1,W1,a3,a2,a1,a0)
    N1:=Q1*S1-T1; N2:=R1*S1; N3:=S1; N4:=T1;
    B:=2*(N1*N4-N2*N3);
    if B eq 0 then
        // "DBL2B0";
        return DBL2B0(Q1,R1,S1,T1,Z1,W1,a3,a2,a1,a0);
    else
        ZZ1:=Z1^2; ZZZZ1:=ZZ1^2;
        ZZZZZZ1:=ZZZZ1*ZZ1;
        QQ1:=Q1^2; SS1:=S1^2; WW1:=W1^2;
        tR1:=2*R1; a3ZZZZ1:=a3*ZZZZ1; tR1mQQ1:=tR1-QQ1;
        N5:=SS1-(Q1*(tR1mQQ1+tR1)-(Q1*a3ZZZZ1-a2*ZZZZZZ1))*WW1;
        N6:=(tR1mQQ1-2*QQ1-a3ZZZZ1)*WW1;
        A:=N1*N5-N2*N6; C:=N3*N5-N4*N6;
        if C eq 0 then
            // "DBL2C0";
            return DBL2C0(Q1,R1,S1,T1,Z1,W1,A,B,a3,a2);
        else
            // "DBL2G";
            return DBL2G(Q1,R1,S1,T1,Z1,W1,A,B,C,a3,a2);
        end if;
    end if;
end function;

ADD22PPMQ:=function(Q1,R1,S1,T1,Z1,W1,Q2,R2,S2,T2,Z2,W2,a3,a2,a1,a0)
    // "ADD22PPMQ";
    ZZ1:=Z1^2; ZZZ1:=ZZ1*Z1; ZZZZZ1:=ZZZ1*ZZ1;
    ZZ2:=Z2^2; ZZZ2:=ZZ2*Z2; ZZZZZ2:=ZZZ2*ZZ2;
    S1ZZZ2:=S1*ZZZ2; S2ZZZ1:=S2*ZZZ1;
    S1ZZZ2W2:=S1ZZZ2*W2; S2ZZZ1W1:=S2ZZZ1*W1;
    T1ZZZZZ2:=T1*ZZZZZ2; T2ZZZZZ1:=T2*ZZZZZ1;
    T1ZZZZZ2W2:=T1ZZZZZ2*W2; T2ZZZZZ1W1:=T2ZZZZZ1*W1;
    K:=S1ZZZ2W2-S2ZZZ1W1; KK:=K^2; KKK:=KK*K;
    X5:=(T2ZZZZZ1W1-T1ZZZZZ2W2)*K;
    Y5:=(T1ZZZZZ2*KK+S1ZZZ2*X5)*KKK;
    Z5:=K*Z1*Z2; W5:=W1;
    XX5:=X5^2; XXXX5:=XX5^2; XXXXX5:=XXXX5*X5; a3XX5:=a3*XX5;
    ZZ5:=Z5^2; ZZZZ5:=ZZ5^2;
    Q3:=-2*X5;
    R3:=XX5;
    S3:=(((a1*ZZ5+2*a2*X5)*ZZ5+3*a3XX5)*ZZZZ5+5*XXXX5)*W5;
    T3:=(((2*a0*ZZ5+a1*X5)*ZZZZ5-a3XX5*X5)*ZZZZ5-3*XXXXX5)*W5;
    Z3:=Z5;
    W3:=2*Y5;
    return Q3,R3,S3,T3,Z3,W3,2;
end function;

ADD22B0:=function(Q1,R1,S1,T1,Z1,W1,Q2,R2,S2,T2,Z2,W2,a3,a2,a1,a0)
    ZZ1:=Z1^2; ZZZZ1:=ZZ1^2; ZZ2:=Z2^2; ZZZZ2:=ZZ2^2;
    Q1ZZ2:=Q1*ZZ2; Q2ZZ1:=Q2*ZZ1; R1ZZZZ2:=R1*ZZZZ2; R2ZZZZ1:=R2*ZZZZ1;
    N1:=Q1ZZ2-Q2ZZ1; N2:=R1ZZZZ2-R2ZZZZ1;
    N1Z1:=N1*Z1; N1Z2:=N1*Z2; NN1ZZ1:=N1Z1^2; NN1ZZ2:=N1Z2^2;
    NNN1ZZZ1:=NN1ZZ1*N1Z1; NNN1ZZZ2:=NN1ZZ2*N1Z2;
    T1NN1ZZ2:=T1*NN1ZZ2; T2NN1ZZ1:=T2*NN1ZZ1;
    XP1:=-N1*N2; YP1:=(S1*XP1+T1NN1ZZ2)*NNN1ZZZ2; ZP1:=N1Z1*Z2; WP1:=W1;
    XP3:=XP1; YP3:=(S2*XP3+T2NN1ZZ1)*NNN1ZZZ1; ZP3:=ZP1; WP3:=W2;
    XP2:=-Q1*NN1ZZ2-XP1; YP2:=(S1*XP2+T1NN1ZZ2)*NNN1ZZZ2; ZP2:=ZP1; WP2:=W1;
    XP4:=-Q2*NN1ZZ1-XP3; YP4:=(S2*XP4+T2NN1ZZ1)*NNN1ZZZ1; ZP4:=ZP1; WP4:=W2;
    YP1WP3:=YP1*WP3; YP3WP1:=YP3*WP1;
    if YP1WP3 eq -YP3WP1 then
        return ADD11(XP2,YP2,ZP2,WP2,XP4,YP4,ZP4,WP4,a3,a2,a1,a0);
    else
        QQ,RR,SS,TT,ZZ,WW,__:=ADD11DBL(XP1,YP1,ZP1,WP1,a3,a2,a1,a0);
        QQ,RR,SS,TT,ZZ,WW,__:=ADD12(XP2,YP2,ZP2,WP2,QQ,RR,SS,TT,ZZ,WW,a3,a2,a1,a0);
        return ADD12(XP4,YP4,ZP4,WP4,QQ,RR,SS,TT,ZZ,WW,a3,a2,a1,a0);
    end if;
end function;

ADD22C0:=function(Q1,R1,S1,T1,Z1,W1,Q2,R2,S2,T2,Z2,W2,A,B)
    ZZ1:=Z1^2; ZZ2:=Z2^2; ZZZ2:=ZZ2*Z2; ZZZZ2:=ZZ2^2; ZZZZZ2:=ZZZZ2*Z2;
    Q1ZZ2:=Q1*ZZ2; Q2ZZ1:=Q2*ZZ1; R1ZZZZ2:=R1*ZZZZ2;
    S1ZZZ2:=S1*ZZZ2; T1ZZZZZ2:=T1*ZZZZZ2;
    BW2:=B*W2; BW1W2:=BW2*W1; BBWW1WW2:=BW1W2^2;
    X3:=(Q1ZZ2+Q2ZZ1)*BBWW1WW2+A^2;
    Y3:=(A*(Q1ZZ2*BBWW1WW2+X3)-S1ZZZ2*BW2*BBWW1WW2)*X3+(A*R1ZZZZ2-T1ZZZZZ2*BW2)*BBWW1WW2^2;
    Z3:=BW1W2*Z1*Z2;
    W3:=1;
    return X3,__,Y3,__,Z3,W3,1;
end function;

ADD22G:=function(Q1,R1,S1,T1,Z1,W1,Q2,R2,S2,T2,Z2,W2,A,B,C)
    ZZ1:=Z1^2; ZZZ1:=ZZ1*Z1;
    ZZ2:=Z2^2; ZZZ2:=ZZ2*Z2; ZZZZ2:=ZZ2^2; ZZZZZ2:=ZZZZ2*Z2;
    Q1ZZ2:=Q1*ZZ2; Q2ZZ1:=Q2*ZZ1; R1ZZZZ2:=R1*ZZZZ2;
    S1ZZZ2W2:=S1*ZZZ2*W2; S2ZZZ1W1:=S2*ZZZ1*W1; T1ZZZZZ2W2:=T1*ZZZZZ2*W2;
    PP:=B*W1*W2; PP2:=PP^2; AC:=A*C;
    CC:=C^2; CCC:=CC*C; CCCC:=CC^2; CCCCC:=CCCC*C;
    BCCC:=B*CCC; D:=(Q1ZZ2-Q2ZZ1)*CC+AC;
    Q3:=D+AC-PP2;
    R3:=AC*D-(S1ZZZ2W2+S2ZZZ1W1)*BCCC+(Q1ZZ2+Q2ZZ1)*PP2*CC;
    QZCmQ3:=Q1ZZ2*CC-Q3;
    RZCmR3:=R1ZZZZ2*CCCC-R3;
    S3:=RZCmR3+(AC-Q3)*QZCmQ3-S1ZZZ2W2*BCCC;
    T3:=RZCmR3*AC-R3*QZCmQ3-T1ZZZZZ2W2*B*CCCCC;
    Z3:=Z2*Z1*C;
    W3:=PP;
    return Q3,R3,S3,T3,Z3,W3,2;
end function;

ADD22:=function(Q1,R1,S1,T1,Z1,W1,Q2,R2,S2,T2,Z2,W2,a3,a2,a1,a0)
    ZZ1:=Z1^2; ZZZZ1:=ZZ1^2; ZZ2:=Z2^2; ZZZZ2:=ZZ2^2;
    Q1ZZ2:=Q1*ZZ2; Q2ZZ1:=Q2*ZZ1;
    R1ZZZZ2:=R1*ZZZZ2; R2ZZZZ1:=R2*ZZZZ1;
    N1:=Q1ZZ2-Q2ZZ1; N2:=R1ZZZZ2-R2ZZZZ1;
    B:=N1*(Q2ZZ1*R1ZZZZ2-Q1ZZ2*R2ZZZZ1)-N2^2;
    if B eq 0 then
        // "ADD22B0";
        return ADD22B0(Q1,R1,S1,T1,Z1,W1,Q2,R2,S2,T2,Z2,W2,a3,a2,a1,a0);
    else
        ZZZ1:=ZZ1*Z1; ZZZZZ1:=ZZZ1*ZZ1; ZZZ2:=ZZ2*Z2; ZZZZZ2:=ZZZ2*ZZ2;
        S1ZZZ2:=S1*ZZZ2; S2ZZZ1:=S2*ZZZ1;
        S1ZZZ2W2:=S1ZZZ2*W2; S2ZZZ1W1:=S2ZZZ1*W1;
        T1ZZZZZ2:=T1*ZZZZZ2; T2ZZZZZ1:=T2*ZZZZZ1;
        T1ZZZZZ2W2:=T1ZZZZZ2*W2; T2ZZZZZ1W1:=T2ZZZZZ1*W1;
        N3:=S1ZZZ2W2-S2ZZZ1W1; N4:=T1ZZZZZ2W2-T2ZZZZZ1W1; N5:=N4*Q2ZZ1-N3*R2ZZZZ1;
        A:=N1*N5-N2*N4; C:=N1*N4-N2*N3;
        if C eq 0 then
            // "ADD22C0";
            return ADD22C0(Q1,R1,S1,T1,Z1,W1,Q2,R2,S2,T2,Z2,W2,A,B);
        else
            // "ADD22G";
            return ADD22G(Q1,R1,S1,T1,Z1,W1,Q2,R2,S2,T2,Z2,W2,A,B,C);
        end if;
    end if;
end function;

ADDDIVISOR:=function(P,dP,Q,dQ,a3,a2,a1,a0)
	if dP eq 0 then
        return getcoords(Q,dQ);
    elif dQ eq 0 then
        return getcoords(P,dP);
    elif dP eq 1 and dQ eq 1 then
        X1,__,Y1,__,Z1,W1,__:=getcoords(P,dP);
        X2,__,Y2,__,Z2,W2,__:=getcoords(Q,dQ);
        return ADD11(X1,Y1,Z1,W1,X2,Y2,Z2,W2,a3,a2,a1,a0);
    elif dP+dQ eq 3 then
        if dP eq 2 then
            P,Q,dP,dQ:=swap(P,Q,dP,dQ);
        end if;
        X1,__,Y1,__,Z1,W1,__:=getcoords(P,dP);
        Q2,R2,S2,T2,Z2,W2,__:=getcoords(Q,dQ);
        return ADD12(X1,Y1,Z1,W1,Q2,R2,S2,T2,Z2,W2,a3,a2,a1,a0);
    elif dP eq 2 and dQ eq 2 then
        Q1,R1,S1,T1,Z1,W1,__:=getcoords(P,dP);
        Q2,R2,S2,T2,Z2,W2,__:=getcoords(Q,dQ);
        // 16M + 4S + 0m
        ZZ1:=Z1^2; ZZZ1:=ZZ1*Z1; ZZZZ1:=ZZ1^2; ZZZZZ1:=ZZZ1*ZZ1;
        ZZ2:=Z2^2; ZZZ2:=ZZ2*Z2; ZZZZ2:=ZZ2^2; ZZZZZ2:=ZZZ2*ZZ2;
        Q1ZZ2:=Q1*ZZ2; Q2ZZ1:=Q2*ZZ1;
        R1ZZZZ2:=R1*ZZZZ2; R2ZZZZ1:=R2*ZZZZ1;
        S1ZZZ2:=S1*ZZZ2; S2ZZZ1:=S2*ZZZ1;
        S1ZZZ2W2:=S1ZZZ2*W2; S2ZZZ1W1:=S2ZZZ1*W1;
        T1ZZZZZ2:=T1*ZZZZZ2; T2ZZZZZ1:=T2*ZZZZZ1;
        T1ZZZZZ2W2:=T1ZZZZZ2*W2; T2ZZZZZ1W1:=T2ZZZZZ1*W1;
        if Q1ZZ2 eq Q2ZZ1 and R1ZZZZ2 eq R2ZZZZ1 then
            if S1ZZZ2W2 eq -S2ZZZ1W1 and T1ZZZZZ2W2 eq -T2ZZZZZ1W1 then
                return 1,__,0,__,0,1,0;
            elif S1ZZZ2W2 eq S2ZZZ1W1 and T1ZZZZZ2W2 eq T2ZZZZZ1W1 then
                return DBL2(Q1,R1,S1,T1,Z1,W1,a3,a2,a1,a0);
            else
                return ADD22PPMQ(Q1,R1,S1,T1,Z1,W1,Q2,R2,S2,T2,Z2,W2,a3,a2,a1,a0);
            end if;
        else
            return ADD22(Q1,R1,S1,T1,Z1,W1,Q2,R2,S2,T2,Z2,W2,a3,a2,a1,a0);
        end if;
    end if;
end function;

// ############# TEST #############

addDivisorTest:=procedure(s,n)
    for i:=1 to n do
        repeat
            repeat
                q:=RandomPrime(s);
            until q ne 7;
            Fq:=GF(q);
            PR<x>:=PolynomialRing(Fq);
            a3:=Random(Fq); a2:=Random(Fq); a1:=Random(Fq); a0:=Random(Fq);
            f:=x^5+a3*x^3+a2*x^2+a1*x+a0; h:=0;
            isCurveValid:=true;
            try 
                E:=HyperellipticCurve(f,h);
            catch e
                isCurveValid:=false;
            end try;
        until isCurveValid;
        g:=Genus(E); J:=Jacobian(E); E;
        for d1 in Points(J) do
            if Degree(d1[1]) eq 0 then
                DD1:=[]; dDD1:=0; D1:=J!0;
            elif Degree(d1[1]) eq 1 then
                x1:=-Coefficient(d1[1],0); y1:=Coefficient(d1[2],0);
                DD1:=[x1,y1,1,1]; dDD1:=1; D1:=d1;
            elif Degree(d1[1]) eq 2 then
                q1:=Coefficient(d1[1],1); r1:=Coefficient(d1[1],0);
                s1:=Coefficient(d1[2],1); t1:=Coefficient(d1[2],0);
                DD1:=[q1,r1,s1,t1,1,1]; dDD1:=2; D1:=d1;
            else
                print "Something wrong";
                assert false;
            end if;
            for d2 in Points(J) do
                Z2:=Random(Fq); W2:=Random(Fq);
                if Degree(d2[1]) eq 0 then
                    DD2:=[]; dDD2:=0; D2:=J!0;
                elif Degree(d2[1]) eq 1 then
                    x2:=-Coefficient(d2[1],0); y2:=Coefficient(d2[2],0);
                    DD2:=[x2,y2,1,1]; dDD2:=1; D2:=d2;
                elif Degree(d2[1]) eq 2 then
                    q2:=Coefficient(d2[1],1); r2:=Coefficient(d2[1],0);
                    s2:=Coefficient(d2[2],1); t2:=Coefficient(d2[2],0);
                    DD2:=[q2,r2,s2,t2,1,1]; dDD2:=2; D2:=d2;
                else
                    print "Something wrong";
                    assert false;
                end if;
                // "-----------------------";
                a,b,c,d,e,f,dDD3:=addDivisor(DD1,dDD1,DD2,dDD2,a3,a2,a1,a0);
                if dDD3 eq 0 or e eq 0 or f eq 0 then
                    D3:=J!0;
                elif dDD3 eq 1 then
                    x3:=a; y3:=c; DD3:=[x3,y3];
                    if not IsCoercible(J,[x-x3,y3]) then
                        printCoords(d1,dDD1,d2,dDD2,PR);
                        "Wrong output DD3:",DD3;
                        "Correct output D1+D2:",D1+D2;
                        assert false;
                    end if;
                    D3:=J![x-x3,y3];
                elif dDD3 eq 2 then
                    q3:=a; r3:=b; s3:=c; t3:=d; DD3:=[q3,r3,s3,t3];
                    if not IsCoercible(J,[x^2+q3*x+r3,s3*x+t3]) then
                        printCoords(d1,dDD1,d2,dDD2,PR);
                        "Wrong output DD3:",DD3;
                        "Correct output D1+D2:",D1+D2;
                        assert false;
                    end if;
                    D3:=J![x^2+q3*x+r3,s3*x+t3];
                end if;
                if D1+D2 ne D3 then
                    printCoords(d1,dDD1,d2,dDD2,PR);
                    "Wrong output DD3:",DD3;
                    "Correct output D1+D2:",D1+D2;
                    assert false;
                end if;
            end for;
        end for;
    end for;
end procedure;

ADDDIVISORTEST:=procedure(s,n)
    for i:=1 to n do
        repeat
            repeat
                q:=RandomPrime(s);
            until q ne 2;
            Fq:=GF(q);
            PR<x>:=PolynomialRing(Fq);
            a3:=Random(Fq); a2:=Random(Fq); a1:=Random(Fq); a0:=Random(Fq);
            f:=x^5+a3*x^3+a2*x^2+a1*x+a0; h:=0;
            isCurveValid:=true;
            try 
                E:=HyperellipticCurve(f,h);
            catch e
                isCurveValid:=false;
            end try;
        until isCurveValid;
        g:=Genus(E); J:=Jacobian(E); E;
        for d1 in Points(J) do
            Z1:=Random(Fq); W1:=Random(Fq);
            if Degree(d1[1]) eq 0 or Z1 eq 0 or W1 eq 0 then
                DD1:=[]; dDD1:=0; D1:=J!0;
            elif Degree(d1[1]) eq 1 then
                x1:=-Coefficient(d1[1],0); y1:=Coefficient(d1[2],0);
                DD1:=[x1*Z1^2,y1*Z1^5*W1,Z1,W1]; dDD1:=1; D1:=d1;
            elif Degree(d1[1]) eq 2 then
                q1:=Coefficient(d1[1],1); r1:=Coefficient(d1[1],0);
                s1:=Coefficient(d1[2],1); t1:=Coefficient(d1[2],0);
                DD1:=[q1*Z1^2,r1*Z1^4,s1*Z1^3*W1,t1*Z1^5*W1,Z1,W1]; dDD1:=2; D1:=d1;
            else
                print "Something wrong";
                assert false;
            end if;
            for d2 in Points(J) do
                Z2:=Random(Fq); W2:=Random(Fq);
                if Degree(d2[1]) eq 0 or Z2 eq 0 or W2 eq 0 then
                    DD2:=[]; dDD2:=0; D2:=J!0;
                elif Degree(d2[1]) eq 1 then
                    x2:=-Coefficient(d2[1],0); y2:=Coefficient(d2[2],0);
                    DD2:=[x2*Z2^2,y2*Z2^5*W2,Z2,W2]; dDD2:=1; D2:=d2;
                elif Degree(d2[1]) eq 2 then
                    q2:=Coefficient(d2[1],1); r2:=Coefficient(d2[1],0);
                    s2:=Coefficient(d2[2],1); t2:=Coefficient(d2[2],0);
                    DD2:=[q2*Z2^2,r2*Z2^4,s2*Z2^3*W2,t2*Z2^5*W2,Z2,W2]; dDD2:=2; D2:=d2;
                else
                    print "Something wrong";
                    assert false;
                end if;
                // "-----------------------";
                a,b,c,d,e,f,dDD3:=ADDDIVISOR(DD1,dDD1,DD2,dDD2,a3,a2,a1,a0);
                if dDD3 eq 0 or e eq 0 or f eq 0 then
                    D3:=J!0;
                elif dDD3 eq 1 then
                    X3:=a; Y3:=c; Z3:=e; W3:=f; DD3:=[X3,Y3,Z3,W3];
                    if not IsCoercible(J,[x-X3/Z3^2,Y3/(Z3^5*W3)]) then
                        printCoords(d1,dDD1,d2,dDD2,PR);
                        "Wrong output DD3:",DD3;
                        "Correct output D1+D2:",D1+D2;
                        assert false;
                    end if;
                    D3:=J![x-X3/Z3^2,Y3/(Z3^5*W3)];
                elif dDD3 eq 2 then
                    Q3:=a; R3:=b; S3:=c; T3:=d; Z3:=e; W3:=f; DD3:=[Q3,R3,S3,T3,Z3,W3];
                    if not IsCoercible(J,[x^2+Q3/Z3^2*x+R3/Z3^4,S3/(Z3^3*W3)*x+T3/(Z3^5*W3)]) then
                        printCoords(d1,dDD1,d2,dDD2,PR);
                        "Wrong output DD3:",DD3;
                        "Correct output D1+D2:",D1+D2;
                        assert false;
                    end if;
                    D3:=J![x^2+Q3/Z3^2*x+R3/Z3^4,S3/(Z3^3*W3)*x+T3/(Z3^5*W3)];
                end if;
                if D1+D2 ne D3 then
                    "Coerced.",Fq;
                    "D3",D3;
                    printCoords(d1,dDD1,d2,dDD2,PR);
                    "Wrong output DD3:",DD3;
                    "Correct output D1+D2:",D1+D2;
                    assert false;
                end if;
            end for;
        end for;
    end for;
end procedure;

primeSize:=4; times:=10;
printf "primeSize: %o\n",primeSize;
addDivisorTest(primeSize,times);
printf "addDivisorTest was Successful for %o times\n",times;
ADDDIVISORTEST(primeSize,times);
printf "ADDDIVISORTEST was Successful for %o times\n",times;
