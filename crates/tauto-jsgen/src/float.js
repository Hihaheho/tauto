// `Float`'s functions: the same algorithms as `crates/tauto-rt/src/float_math.rs`,
// operation for operation, so that a program prints the same digits under
// every backend. The engine's own `Math.sin`, `Math.log`, … are not used:
// engines differ from each other and from the Rust backend in the last bit.
//
// Derived from the same sources as `float_math.rs`: the `libm` crate (MIT OR
// Apache-2.0), musl libc and FreeBSD's msun; see NOTICE.
// ====================================================
// Copyright (C) 1993, 2004 by Sun Microsystems, Inc. All rights reserved.
//
// Developed at SunPro, a Sun Microsystems, Inc. business.
// Permission to use, copy, modify, and distribute this
// software is freely granted, provided that this notice
// is preserved.
// ====================================================
const floatMath=(()=>{
    const F=new Float64Array(1),U=new Uint32Array(F.buffer);
    const LE=new Uint8Array(new Uint16Array([1]).buffer)[0]===1,H=LE?1:0,L=LE?0:1;
    const hi=x=>{F[0]=x;return U[H];};
    const lo=x=>{F[0]=x;return U[L];};
    const words=(h,l)=>{U[H]=h;U[L]=l;return F[0];};
    const setHi=(x,h)=>{F[0]=x;U[H]=h;return F[0];};
    const setLo=(x,l)=>{F[0]=x;U[L]=l;return F[0];};
    const scalbn=(x,n)=>{
        const x1p1023=words(0x7fe00000,0),x1p53=words(0x43400000,0),x1p_1022=words(0x00100000,0);
        let y=x;
        if(n>1023){y*=x1p1023;n-=1023;if(n>1023){y*=x1p1023;n-=1023;if(n>1023)n=1023;}}
        else if(n< -1022){y*=x1p_1022*x1p53;n+=1022-53;if(n< -1022){y*=x1p_1022*x1p53;n+=1022-53;if(n< -1022)n=-1022;}}
        return y*words((0x3ff+n)<<20>>>0,0);
    };
    const kSin=(x,y,iy)=>{
        const S1=-1.66666666666666324348e-01,S2=8.33333333332248946124e-03,S3=-1.98412698298579493134e-04,
            S4=2.75573137070700676789e-06,S5=-2.50507602534068634195e-08,S6=1.58969099521155010221e-10;
        const z=x*x,w=z*z,r=S2+z*(S3+z*S4)+z*w*(S5+z*S6),v=z*x;
        return iy===0?x+v*(S1+z*r):x-((z*(0.5*y-v*r)-y)-v*S1);
    };
    const kCos=(x,y)=>{
        const C1=4.16666666666666019037e-02,C2=-1.38888888888741095749e-03,C3=2.48015872894767294178e-05,
            C4=-2.75573143513906633035e-07,C5=2.08757232129817482790e-09,C6=-1.13596475577881948265e-11;
        const z=x*x,w=z*z,r=z*(C1+z*(C2+z*C3))+w*w*(C4+z*(C5+z*C6)),hz=0.5*z,w1=1.0-hz;
        return w1+(((1.0-w1)-hz)+(z*r-x*y));
    };
    const T=[3.33333333333334091986e-01,1.33333333333201242699e-01,5.39682539762260521377e-02,
        2.18694882948595424599e-02,8.86323982359930005737e-03,3.59207910759131235356e-03,
        1.45620945432529025516e-03,5.88041240820264096874e-04,2.46463134818469906812e-04,
        7.81794442939557092300e-05,7.14072491382608190305e-05,-1.85586374855275456654e-05,
        2.59073051863633712884e-05];
    const kTan=(x,y,odd)=>{
        const PIO4=7.85398163397448278999e-01,PIO4_LO=3.06161699786838301793e-17;
        const hx=hi(x),big=(hx&0x7fffffff)>=0x3FE59428;
        if(big){if(hx>>>31){x=-x;y=-y;}x=(PIO4-x)+(PIO4_LO-y);y=0.0;}
        const z=x*x,w=z*z;
        let r=T[1]+w*(T[3]+w*(T[5]+w*(T[7]+w*(T[9]+w*T[11]))));
        let v=z*(T[2]+w*(T[4]+w*(T[6]+w*(T[8]+w*(T[10]+w*T[12])))));
        const s=z*x;
        r=y+z*(s*(r+v)+y)+s*T[0];
        const w1=x+r;
        if(big){const s1=1.0-2.0*odd;v=s1-2.0*(x+(r-w1*w1/(w1+s1)));return hx>>>31?-v:v;}
        if(odd===0)return w1;
        const w0=setLo(w1,0);v=r-(w0-x);
        const a=-1.0/w1,a0=setLo(a,0);
        return a0+a*(1.0+a0*w0+a0*v);
    };
    const INIT_JK=[3,4,4,6];
    const IPIO2=[0xA2F983,0x6E4E44,0x1529FC,0x2757D1,0xF534DD,0xC0DB62,0x95993C,0x439041,0xFE5163,
        0xABDEBB,0xC561B7,0x246E3A,0x424DD2,0xE00649,0x2EEA09,0xD1921C,0xFE1DEB,0x1CB129,
        0xA73EE8,0x8235F5,0x2EBB44,0x84E99C,0x7026B4,0x5F7E41,0x3991D6,0x398353,0x39F49C,
        0x845F8B,0xBDF928,0x3B1FF8,0x97FFDE,0x05980F,0xEF2F11,0x8B5A0A,0x6D1F6D,0x367ECF,
        0x27CB09,0xB74F46,0x3F669E,0x5FEA2D,0x7527BA,0xC7EBE5,0xF17B3D,0x0739F7,0x8A5292,
        0xEA6BFB,0x5FB11F,0x8D5D08,0x560330,0x46FC7B,0x6BABF0,0xCFBC20,0x9AF436,0x1DA9E3,
        0x91615E,0xE61B08,0x659985,0x5F14A0,0x68408D,0xFFD880,0x4D7327,0x310606,0x1556CA,
        0x73A8C9,0x60E27B,0xC08C6B];
    const PIO2=[1.57079625129699707031e+00,7.54978941586159635335e-08,5.39030252995776476554e-15,
        3.28200341580791294123e-22,1.27065575308067607349e-29,1.22933308981111328932e-36,
        2.73370053816464559624e-44,2.16741683877804819444e-51];
    // `y` gets the result; `prec` is 1 here (a double's two pieces).
    const remPio2Large=(x,y,e0,prec)=>{
        const x1p24=words(0x41700000,0),x1p_24=words(0x3e700000,0);
        const nx=x.length,f=new Array(20).fill(0),fq=new Array(20).fill(0),q=new Array(20).fill(0),iq=new Array(20).fill(0);
        let fw,n,ih,z;
        const jk=INIT_JK[prec],jp=jk,jx=nx-1;
        let jv=Math.trunc((e0-3)/24);if(jv<0)jv=0;
        let q0=e0-24*(jv+1);
        let j=jv-jx;const m=jx+jk;
        for(let i=0;i<=m;i++){f[i]=j<0?0:IPIO2[j];j++;}
        for(let i=0;i<=jk;i++){fw=0;for(let j=0;j<=jx;j++)fw+=x[j]*f[jx+i-j];q[i]=fw;}
        let jz=jk;
        for(;;){
            let i=0;z=q[jz];
            for(let j=jz;j>=1;j--){fw=Math.trunc(x1p_24*z);iq[i]=Math.trunc(z-x1p24*fw);z=q[j-1]+fw;i++;}
            z=scalbn(z,q0);z-=8.0*Math.floor(z*0.125);
            n=Math.trunc(z);z-=n;ih=0;
            if(q0>0){i=iq[jz-1]>>(24-q0);n+=i;iq[jz-1]-=i<<(24-q0);ih=iq[jz-1]>>(23-q0);}
            else if(q0===0)ih=iq[jz-1]>>23;
            else if(z>=0.5)ih=2;
            if(ih>0){
                n+=1;let carry=0;
                for(let i=0;i<jz;i++){const j=iq[i];if(carry===0){if(j!==0){carry=1;iq[i]=0x1000000-j;}}else iq[i]=0xffffff-j;}
                if(q0>0){if(q0===1)iq[jz-1]&=0x7fffff;else if(q0===2)iq[jz-1]&=0x3fffff;}
                if(ih===2){z=1-z;if(carry!==0)z-=scalbn(1,q0);}
            }
            if(z===0){
                let j=0;for(let i=jz-1;i>=jk;i--)j|=iq[i];
                if(j===0){
                    let k=1;while(iq[jk-k]===0)k++;
                    for(let i=jz+1;i<=jz+k;i++){f[jx+i]=IPIO2[jv+i];fw=0;for(let j=0;j<=jx;j++)fw+=x[j]*f[jx+i-j];q[i]=fw;}
                    jz+=k;continue;
                }
            }
            break;
        }
        if(z===0){jz-=1;q0-=24;while(iq[jz]===0){jz-=1;q0-=24;}}
        else{
            z=scalbn(z,-q0);
            if(z>=x1p24){fw=Math.trunc(x1p_24*z);iq[jz]=Math.trunc(z-x1p24*fw);jz+=1;q0+=24;iq[jz]=Math.trunc(fw);}
            else iq[jz]=Math.trunc(z);
        }
        fw=scalbn(1,q0);
        for(let i=jz;i>=0;i--){q[i]=fw*iq[i];fw*=x1p_24;}
        for(let i=jz;i>=0;i--){fw=0;let k=0;while(k<=jp&&k<=jz-i){fw+=PIO2[k]*q[i+k];k++;}fq[jz-i]=fw;}
        fw=0;for(let i=jz;i>=0;i--)fw+=fq[i];
        y[0]=ih===0?fw:-fw;
        fw=fq[0]-fw;for(let i=1;i<=jz;i++)fw+=fq[i];
        y[1]=ih===0?fw:-fw;
        return n&7;
    };
    const remPio2=x=>{
        const TO_INT=1.5/2.2204460492503131e-16,INV_PIO2=6.36619772367581382433e-01,
            PIO2_1=1.57079632673412561417e+00,PIO2_1T=6.07710050650619224932e-11,
            PIO2_2=6.07710050630396597660e-11,PIO2_2T=2.02226624879595063154e-21,
            PIO2_3=2.02226624871116645580e-21,PIO2_3T=8.47842766036889956997e-32;
        const x1p24=words(0x41700000,0);
        const h=hi(x),sign=h>>>31,ix=h&0x7fffffff;
        const medium=()=>{
            const fn=(x*INV_PIO2+TO_INT)-TO_INT,n=Math.trunc(fn);
            let r=x-fn*PIO2_1,w=fn*PIO2_1T,y0=r-w;
            const ex=ix>>>20;
            if(ex-((hi(y0)>>>20)&0x7ff)>16){
                let t=r;w=fn*PIO2_2;r=t-w;w=fn*PIO2_2T-((t-r)-w);y0=r-w;
                if(ex-((hi(y0)>>>20)&0x7ff)>49){t=r;w=fn*PIO2_3;r=t-w;w=fn*PIO2_3T-((t-r)-w);y0=r-w;}
            }
            return [n,y0,(r-y0)-w];
        };
        const near=k=>{
            if(sign===0){const z=x-k*PIO2_1,y0=z-k*PIO2_1T;return [k,y0,(z-y0)-k*PIO2_1T];}
            const z=x+k*PIO2_1,y0=z+k*PIO2_1T;return [-k,y0,(z-y0)+k*PIO2_1T];
        };
        if(ix<=0x400f6a7a){
            if((ix&0xfffff)===0x921fb)return medium();
            return near(ix<=0x4002d97c?1:2);
        }
        if(ix<=0x401c463b){
            if(ix<=0x4015fdbc){if(ix===0x4012d97c)return medium();return near(3);}
            if(ix===0x401921fb)return medium();
            return near(4);
        }
        if(ix<0x413921fb)return medium();
        if(ix>=0x7ff00000){const y0=x-x;return [0,y0,y0];}
        let z=words((hi(x)&0x000fffff)|((0x3ff+23)<<20),lo(x));
        const tx=[0,0,0];
        for(let i=0;i<2;i++){tx[i]=Math.trunc(z);z=(z-tx[i])*x1p24;}
        tx[2]=z;
        let i=2;while(i!==0&&tx[i]===0)i--;
        const ty=[0,0,0];
        const n=remPio2Large(tx.slice(0,i+1),ty,(ix>>20)-(0x3ff+23),1);
        return sign?[-n,-ty[0],-ty[1]]:[n,ty[0],ty[1]];
    };
    const sin=x=>{
        const ix=hi(x)&0x7fffffff;
        if(ix<=0x3fe921fb){if(ix<0x3e500000)return x;return kSin(x,0,0);}
        if(ix>=0x7ff00000)return x-x;
        const [n,y0,y1]=remPio2(x);
        switch(n&3){case 0:return kSin(y0,y1,1);case 1:return kCos(y0,y1);case 2:return -kSin(y0,y1,1);default:return -kCos(y0,y1);}
    };
    const cos=x=>{
        const ix=hi(x)&0x7fffffff;
        if(ix<=0x3fe921fb){if(ix<0x3e46a09e&&Math.trunc(x)===0)return 1;return kCos(x,0);}
        if(ix>=0x7ff00000)return x-x;
        const [n,y0,y1]=remPio2(x);
        switch(n&3){case 0:return kCos(y0,y1);case 1:return -kSin(y0,y1,1);case 2:return -kCos(y0,y1);default:return kSin(y0,y1,1);}
    };
    const tan=x=>{
        const ix=hi(x)&0x7fffffff;
        if(ix<=0x3fe921fb){if(ix<0x3e400000)return x;return kTan(x,0,0);}
        if(ix>=0x7ff00000)return x-x;
        const [n,y0,y1]=remPio2(x);
        return kTan(y0,y1,n&1);
    };
    const exp=x=>{
        const HALF=[0.5,-0.5],LN2HI=6.93147180369123816490e-01,LN2LO=1.90821492927058770002e-10,
            INVLN2=1.44269504088896338700e+00,P1=1.66666666666666019037e-01,P2=-2.77777777770155933842e-03,
            P3=6.61375632143793436117e-05,P4=-1.65339022054652515390e-06,P5=4.13813679705723846039e-08;
        const x1p1023=words(0x7fe00000,0);
        let hx=hi(x);const sign=hx>>>31;hx&=0x7fffffff;
        if(hx>=0x4086232b){
            if(Number.isNaN(x))return x;
            if(x>709.782712893383973096)return x*x1p1023;
            if(x< -708.39641853226410622&&x< -745.13321910194110842)return 0;
        }
        let k,hi1,lo1;
        if(hx>0x3fd62e42){
            k=hx>=0x3ff0a2b2?Math.trunc(INVLN2*x+HALF[sign]):1-sign-sign;
            hi1=x-k*LN2HI;lo1=k*LN2LO;x=hi1-lo1;
        }else if(hx>0x3e300000){k=0;hi1=x;lo1=0;}
        else return 1+x;
        const xx=x*x,c=x-xx*(P1+xx*(P2+xx*(P3+xx*(P4+xx*P5)))),y=1+(x*c/(2-c)-lo1+hi1);
        return k===0?y:scalbn(y,k);
    };
    const expm1=x=>{
        const O_THRESHOLD=7.09782712893383973096e+02,LN2_HI=6.93147180369123816490e-01,LN2_LO=1.90821492927058770002e-10,
            INVLN2=1.44269504088896338700e+00,Q1=-3.33333333333331316428e-02,Q2=1.58730158725481460165e-03,
            Q3=-7.93650757867487942473e-05,Q4=4.00821782732936239552e-06,Q5=-2.01099218183624371326e-07;
        const h=hi(x),hx=h&0x7fffffff,sign=h>>>31;
        let hi1,lo1,k,c,t,y;
        if(hx>=0x4043687A){
            if(Number.isNaN(x))return x;
            if(sign)return -1;
            if(x>O_THRESHOLD)return x*words(0x7fe00000,0);
        }
        if(hx>0x3fd62e42){
            if(hx<0x3FF0A2B2){
                if(sign===0){hi1=x-LN2_HI;lo1=LN2_LO;k=1;}else{hi1=x+LN2_HI;lo1=-LN2_LO;k=-1;}
            }else{
                k=Math.trunc(INVLN2*x+(sign?-0.5:0.5));t=k;hi1=x-t*LN2_HI;lo1=t*LN2_LO;
            }
            x=hi1-lo1;c=(hi1-x)-lo1;
        }else if(hx<0x3c900000)return x;
        else{c=0;k=0;}
        const hfx=0.5*x,hxs=x*hfx,r1=1+hxs*(Q1+hxs*(Q2+hxs*(Q3+hxs*(Q4+hxs*Q5))));
        t=3-r1*hfx;
        let e=hxs*((r1-t)/(6-x*t));
        if(k===0)return x-(x*e-hxs);
        e=x*(e-c)-c;e-=hxs;
        if(k===-1)return 0.5*(x-e)-0.5;
        if(k===1){if(x< -0.25)return -2*(e-(x+0.5));return 1+2*(x-e);}
        const twopk=words(((0x3ff+k)<<20)>>>0,0);
        if(k<0||k>56){
            y=x-e+1;
            y=k===1024?y*2*words(0x7fe00000,0):y*twopk;
            return y-1;
        }
        const uf=words(((0x3ff-k)<<20)>>>0,0);
        return k<20?(x-e+(1-uf))*twopk:(x-(e+uf)+1)*twopk;
    };
    const expo2=x=>{
        const kln2=words(0x40962066,0x151add8b),scale=words(((0x3ff+1021)<<20)>>>0,0);
        return exp(x-kln2)*scale*scale;
    };
    const LG1=6.666666666666735130e-01,LG2=3.999999999940941908e-01,LG3=2.857142874366239149e-01,
        LG4=2.222219843214978396e-01,LG5=1.818357216161805012e-01,LG6=1.531383769920937332e-01,
        LG7=1.479819860511658591e-01;
    // The reduction `log`, `log2` and `log10` share: `x = 2^k (1 + f)`, or the
    // answer when there is one without it.
    const logReduce=x=>{
        let h=hi(x),l=lo(x),k=0;
        if(h<0x00100000||(h>>>31)){
            if(((h&0x7fffffff)|l)===0)return {done:-1/(x*x)};
            if(h>>>31)return {done:(x-x)/0};
            k-=54;x*=words(0x43500000,0);h=hi(x);l=lo(x);
        }else if(h>=0x7ff00000)return {done:x};
        else if(h===0x3ff00000&&l===0)return {done:0};
        h=(h+(0x3ff00000-0x3fe6a09e))>>>0;
        k+=(h>>>20)-0x3ff;
        h=(h&0x000fffff)+0x3fe6a09e;
        return {k,f:words(h,l)-1};
    };
    const log=x=>{
        const r0=logReduce(x);if('done' in r0)return r0.done;
        const {k,f}=r0,LN2_HI=6.93147180369123816490e-01,LN2_LO=1.90821492927058770002e-10;
        const hfsq=0.5*f*f,s=f/(2+f),z=s*s,w=z*z,t1=w*(LG2+w*(LG4+w*LG6)),t2=z*(LG1+w*(LG3+w*(LG5+w*LG7))),r=t2+t1,dk=k;
        return s*(hfsq+r)+dk*LN2_LO-hfsq+f+dk*LN2_HI;
    };
    const log2=x=>{
        const r0=logReduce(x);if('done' in r0)return r0.done;
        const {k,f}=r0,IVLN2HI=1.44269504072144627571e+00,IVLN2LO=1.67517131648865118353e-10;
        const hfsq=0.5*f*f,s=f/(2+f),z=s*s;let w=z*z;
        const t1=w*(LG2+w*(LG4+w*LG6)),t2=z*(LG1+w*(LG3+w*(LG5+w*LG7))),r=t2+t1;
        const hi1=setLo(f-hfsq,0),lo1=f-hi1-hfsq+s*(hfsq+r);
        let valHi=hi1*IVLN2HI,valLo=(lo1+hi1)*IVLN2LO+lo1*IVLN2HI;
        const y=k;w=y+valHi;valLo+=(y-w)+valHi;valHi=w;
        return valLo+valHi;
    };
    const log10=x=>{
        const r0=logReduce(x);if('done' in r0)return r0.done;
        const {k,f}=r0,IVLN10HI=4.34294481878168880939e-01,IVLN10LO=2.50829467116452752298e-11,
            LOG10_2HI=3.01029995663611771306e-01,LOG10_2LO=3.69423907715893078616e-13;
        const hfsq=0.5*f*f,s=f/(2+f),z=s*s;let w=z*z;
        const t1=w*(LG2+w*(LG4+w*LG6)),t2=z*(LG1+w*(LG3+w*(LG5+w*LG7))),r=t2+t1;
        const hi1=setLo(f-hfsq,0),lo1=f-hi1-hfsq+s*(hfsq+r);
        let valHi=hi1*IVLN10HI;const dk=k,y=dk*LOG10_2HI;
        let valLo=dk*LOG10_2LO+(lo1+hi1)*IVLN10LO+lo1*IVLN10HI;
        w=y+valHi;valLo+=(y-w)+valHi;valHi=w;
        return valLo+valHi;
    };
    const pow=(x,y)=>{
        const BP=[1.0,1.5],DP_H=[0.0,5.84962487220764160156e-01],DP_L=[0.0,1.35003920212974897128e-08],
            TWO53=9007199254740992.0,HUGE=1.0e300,TINY=1.0e-300,
            L1=5.99999999999994648725e-01,L2=4.28571428578550184252e-01,L3=3.33333329818377432918e-01,
            L4=2.72728123808534006489e-01,L5=2.30660745775561754067e-01,L6=2.06975017800338417784e-01,
            P1=1.66666666666666019037e-01,P2=-2.77777777770155933842e-03,P3=6.61375632143793436117e-05,
            P4=-1.65339022054652515390e-06,P5=4.13813679705723846039e-08,
            LG2=6.93147180559945286227e-01,LG2_H=6.93147182464599609375e-01,LG2_L=-1.90465429995776804525e-09,
            OVT=8.0085662595372944372e-017,CP=9.61796693925975554329e-01,CP_H=9.61796700954437255859e-01,
            CP_L=-7.02846165095275826516e-09,IVLN2=1.44269504088896338700e+00,IVLN2_H=1.44269502162933349609e+00,
            IVLN2_L=1.92596299112661746887e-08;
        let t1,t2;
        const hx=hi(x)|0,lx=lo(x),hy=hi(y)|0,ly=lo(y);
        let ix=hx&0x7fffffff;const iy=hy&0x7fffffff;
        if((iy|ly)===0)return 1;
        if(hx===0x3ff00000&&lx===0)return 1;
        if(ix>0x7ff00000||(ix===0x7ff00000&&lx!==0)||iy>0x7ff00000||(iy===0x7ff00000&&ly!==0))return x+y;
        let yisint=0,k,j;
        if(hx<0){
            if(iy>=0x43400000)yisint=2;
            else if(iy>=0x3ff00000){
                k=(iy>>20)-0x3ff;
                if(k>20){j=ly>>>(52-k);if(((j<<(52-k))|0)===(ly|0))yisint=2-(j&1);}
                else if(ly===0){j=iy>>(20-k);if((j<<(20-k))===iy)yisint=2-(j&1);}
            }
        }
        if(ly===0){
            if(iy===0x7ff00000){
                if(((ix-0x3ff00000)|lx)===0)return 1;
                if(ix>=0x3ff00000)return hy>=0?y:0;
                return hy>=0?0:-y;
            }
            if(iy===0x3ff00000)return hy>=0?x:1/x;
            if(hy===0x40000000)return x*x;
            if(hy===0x3fe00000&&hx>=0)return Math.sqrt(x);
        }
        let ax=Math.abs(x);
        if(lx===0&&(ix===0x7ff00000||ix===0||ix===0x3ff00000)){
            let z=ax;
            if(hy<0)z=1/z;
            if(hx<0){if(((ix-0x3ff00000)|yisint)===0)z=(z-z)/(z-z);else if(yisint===1)z=-z;}
            return z;
        }
        let s=1;
        if(hx<0){if(yisint===0)return (x-x)/(x-x);if(yisint===1)s=-1;}
        if(iy>0x41e00000){
            if(iy>0x43f00000){
                if(ix<=0x3fefffff)return hy<0?HUGE*HUGE:TINY*TINY;
                if(ix>=0x3ff00000)return hy>0?HUGE*HUGE:TINY*TINY;
            }
            if(ix<0x3fefffff)return hy<0?s*HUGE*HUGE:s*TINY*TINY;
            if(ix>0x3ff00000)return hy>0?s*HUGE*HUGE:s*TINY*TINY;
            const t=ax-1,w=(t*t)*(0.5-t*(0.3333333333333333333333-t*0.25)),u=IVLN2_H*t,v=t*IVLN2_L-w*IVLN2;
            t1=setLo(u+v,0);t2=v-(t1-u);
        }else{
            let n=0;
            if(ix<0x00100000){ax*=TWO53;n-=53;ix=hi(ax)|0;}
            n+=(ix>>20)-0x3ff;j=ix&0x000fffff;
            let kk;ix=j|0x3ff00000;
            if(j<=0x3988E)kk=0;else if(j<0xBB67A)kk=1;else{kk=0;n+=1;ix-=0x00100000;}
            ax=setHi(ax,ix>>>0);
            let u=ax-BP[kk],v=1/(ax+BP[kk]);
            const ss=u*v,sH=setLo(ss,0);
            let tH=words((((ix>>>1)|0x20000000)+0x00080000+(kk<<18))>>>0,0);
            let tL=ax-(tH-BP[kk]);
            const sL=v*((u-sH*tH)-sH*tL);
            let s2=ss*ss;
            let r=s2*s2*(L1+s2*(L2+s2*(L3+s2*(L4+s2*(L5+s2*L6)))));
            r+=sL*(sH+ss);s2=sH*sH;
            tH=setLo(3+s2+r,0);tL=r-((tH-3)-s2);
            u=sH*tH;v=sL*tH+tL*ss;
            const pH=setLo(u+v,0),pL=v-(pH-u),zH=CP_H*pH,zL=CP_L*pH+pL*CP+DP_L[kk],t=n;
            t1=setLo(((zH+zL)+DP_H[kk])+t,0);t2=zL-(((t1-t)-DP_H[kk])-zH);
        }
        const y1=setLo(y,0),pL=(y-y1)*t1+y*t2;
        let pH=y1*t1;
        let z=pL+pH;
        j=hi(z)|0;const i0=lo(z)|0;
        if(j>=0x40900000){
            if(((j-0x40900000)|i0)!==0)return s*HUGE*HUGE;
            if(pL+OVT>z-pH)return s*HUGE*HUGE;
        }else if((j&0x7fffffff)>=0x4090cc00){
            if((((j>>>0)-0xc090cc00)|i0)!==0)return s*TINY*TINY;
            if(pL<=z-pH)return s*TINY*TINY;
        }
        const i=j&0x7fffffff;
        k=(i>>20)-0x3ff;
        let n=0;
        if(i>0x3fe00000){
            n=j+(0x00100000>>(k+1));
            k=((n&0x7fffffff)>>20)-0x3ff;
            const t=words((n&~(0x000fffff>>k))>>>0,0);
            n=((n&0x000fffff)|0x00100000)>>(20-k);
            if(j<0)n=-n;
            pH-=t;
        }
        const t=setLo(pL+pH,0),u=t*LG2_H,v=(pL-(t-pH))*LG2+t*LG2_L;
        z=u+v;
        const w=v-(z-u),tt=z*z,tt1=z-tt*(P1+tt*(P2+tt*(P3+tt*(P4+tt*P5)))),r=(z*tt1)/(tt1-2)-(w+z*w);
        z=1-(r-z);
        j=hi(z)|0;j=(j+(n<<20))|0;
        z=(j>>20)<=0?scalbn(z,n):setHi(z,j>>>0);
        return s*z;
    };
    const cbrt=x=>{
        const B1=715094163,B2=696219795,P0=1.87595182427177009643,P1=-1.88497979543377169875,
            P2=1.621429720105354466140,P3=-0.758397934778766047437,P4=0.145996192886612446982;
        let hx=hi(x)&0x7fffffff;
        if(hx>=0x7ff00000)return x+x;
        if(hx<0x00100000){
            hx=hi(x*words(0x43500000,0))&0x7fffffff;
            if(hx===0)return x;
            hx=Math.floor(hx/3)+B2;
        }else hx=Math.floor(hx/3)+B1;
        let t=words(((hi(x)&0x80000000)|hx)>>>0,0);
        let r=(t*t)*(t/x);
        t=t*((P0+r*(P1+r*P2))+((r*r)*r)*(P3+r*P4));
        // Round t away from zero to 23 bits: (bits + 0x80000000) & 0xffffffffc0000000.
        let h=hi(t),l=lo(t);
        if(l>=0x80000000)h=(h+1)>>>0;
        t=words(h,((l+0x80000000)>>>0)&0xc0000000);
        const s=t*t;r=x/s;const w=t+t;r=(r-t)/(w+r);
        return t+t*r;
    };
    const ATANHI=[4.63647609000806093515e-01,7.85398163397448278999e-01,9.82793723247329054082e-01,1.57079632679489655800e+00];
    const ATANLO=[2.26987774529616870924e-17,3.06161699786838301793e-17,1.39033110312309984516e-17,6.12323399573676603587e-17];
    const AT=[3.33333333333329318027e-01,-1.99999999998764832476e-01,1.42857142725034663711e-01,
        -1.11111104054623557880e-01,9.09088713343650656196e-02,-7.69187620504482999495e-02,
        6.66107313738753120669e-02,-5.83357013379057348645e-02,4.97687799461593236017e-02,
        -3.65315727442169155270e-02,1.62858201153657823623e-02];
    const atan=x=>{
        const h=hi(x),sign=h>>>31,ix=h&0x7fffffff;
        if(ix>=0x44100000){
            if(Number.isNaN(x))return x;
            const z=ATANHI[3]+words(0,0x03800000);
            return sign?-z:z;
        }
        let id;
        if(ix<0x3fdc0000){if(ix<0x3e400000)return x;id=-1;}
        else{
            x=Math.abs(x);
            if(ix<0x3ff30000){
                if(ix<0x3fe60000){x=(2*x-1)/(2+x);id=0;}else{x=(x-1)/(x+1);id=1;}
            }else if(ix<0x40038000){x=(x-1.5)/(1+1.5*x);id=2;}
            else{x=-1/x;id=3;}
        }
        const z=x*x,w=z*z;
        const s1=z*(AT[0]+w*(AT[2]+w*(AT[4]+w*(AT[6]+w*(AT[8]+w*AT[10])))));
        const s2=w*(AT[1]+w*(AT[3]+w*(AT[5]+w*(AT[7]+w*AT[9]))));
        if(id<0)return x-x*(s1+s2);
        const r=ATANHI[id]-(x*(s1+s2)-ATANLO[id]-x);
        return sign?-r:r;
    };
    const atan2=(y,x)=>{
        const PI=3.1415926535897931160E+00,PI_LO=1.2246467991473531772E-16;
        if(Number.isNaN(x)||Number.isNaN(y))return x+y;
        let ix=hi(x);const lx=lo(x);let iy=hi(y);const ly=lo(y);
        if((((ix-0x3ff00000)>>>0)|lx)===0)return atan(y);
        const m=((iy>>>31)&1)|((ix>>>30)&2);
        ix&=0x7fffffff;iy&=0x7fffffff;
        if((iy|ly)===0)return m<2?y:m===2?PI:-PI;
        if((ix|lx)===0)return m&1?-PI/2:PI/2;
        if(ix===0x7ff00000){
            if(iy===0x7ff00000)return [PI/4,-PI/4,3*PI/4,-3*PI/4][m];
            return [0,-0,PI,-PI][m];
        }
        if(((ix+(64<<20))>>>0)<iy||iy===0x7ff00000)return m&1?-PI/2:PI/2;
        const z=(m&2)&&((iy+(64<<20))>>>0)<ix?0:atan(Math.abs(y/x));
        switch(m){case 0:return z;case 1:return -z;case 2:return PI-(z-PI_LO);default:return (z-PI_LO)-PI;}
    };
    const PIO2_HI=1.57079632679489655800e+00,PIO2_LO=6.12323399573676603587e-17;
    const R=z=>{
        const PS0=1.66666666666666657415e-01,PS1=-3.25565818622400915405e-01,PS2=2.01212532134862925881e-01,
            PS3=-4.00555345006794114027e-02,PS4=7.91534994289814532176e-04,PS5=3.47933107596021167570e-05,
            QS1=-2.40339491173441421878e+00,QS2=2.02094576023350569471e+00,QS3=-6.88283971605453293030e-01,
            QS4=7.70381505559019352791e-02;
        const p=z*(PS0+z*(PS1+z*(PS2+z*(PS3+z*(PS4+z*PS5))))),q=1+z*(QS1+z*(QS2+z*(QS3+z*QS4)));
        return p/q;
    };
    const asin=x=>{
        const hx=hi(x),ix=hx&0x7fffffff;
        if(ix>=0x3ff00000){
            if(((ix-0x3ff00000)|lo(x))===0)return x*PIO2_HI+words(0x38700000,0);
            return 0/(x-x);
        }
        if(ix<0x3fe00000){
            if(ix<0x3e500000&&ix>=0x00100000)return x;
            return x+x*R(x*x);
        }
        const z=(1-Math.abs(x))*0.5,s=Math.sqrt(z),r=R(z);
        if(ix>=0x3fef3333)x=PIO2_HI-(2*(s+s*r)-PIO2_LO);
        else{
            const f=setLo(s,0),c=(z-f*f)/(s+f);
            x=0.5*PIO2_HI-(2*s*r-(PIO2_LO-2*c)-(0.5*PIO2_HI-2*f));
        }
        return hx>>>31?-x:x;
    };
    const acos=x=>{
        const x1p_120f=words(0x38700000,0);
        const hx=hi(x),ix=hx&0x7fffffff;
        if(ix>=0x3ff00000){
            if(((ix-0x3ff00000)|lo(x))===0)return hx>>>31?2*PIO2_HI+x1p_120f:0;
            return 0/(x-x);
        }
        if(ix<0x3fe00000){
            if(ix<=0x3c600000)return PIO2_HI+x1p_120f;
            return PIO2_HI-(x-(PIO2_LO-x*R(x*x)));
        }
        if(hx>>>31){
            const z=(1+x)*0.5,s=Math.sqrt(z),w=R(z)*s-PIO2_LO;
            return 2*(PIO2_HI-(s+w));
        }
        const z=(1-x)*0.5,s=Math.sqrt(z),df=setLo(s,0),c=(z-df*df)/(s+df),w=R(z)*s+c;
        return 2*(df+w);
    };
    const sinh=x=>{
        const h=hi(x)>>>31?-0.5:0.5,absx=Math.abs(x),w=hi(absx);
        if(w<0x40862e42){
            const t=expm1(absx);
            if(w<0x3ff00000){
                if(w<0x3ff00000-(26<<20))return x;
                return h*(2*t-t*t/(t+1));
            }
            return h*(t+t/(t+1));
        }
        return 2*h*expo2(absx);
    };
    const cosh=x=>{
        x=Math.abs(x);
        const w=hi(x);
        if(w<0x3fe62e42){
            if(w<0x3ff00000-(26<<20))return 1;
            const t=expm1(x);
            return 1+t*t/(2*(1+t));
        }
        if(w<0x40862e42){const t=exp(x);return 0.5*(t+1/t);}
        return expo2(x);
    };
    const tanh=x=>{
        const sign=hi(x)>>>31;x=Math.abs(x);
        const w=hi(x);let t;
        if(w>0x3fe193ea){
            if(w>0x40340000)t=1-0/x;
            else{t=expm1(2*x);t=1-2/(t+2);}
        }else if(w>0x3fd058ae){t=expm1(2*x);t=t/(t+2);}
        else if(w>=0x00100000){t=expm1(-2*x);t=-t/(t+2);}
        else t=x;
        return sign?-t:t;
    };
    return {sin,cos,tan,asin,acos,atan,atan2,exp,log,log2,log10,pow,cbrt,sinh,cosh,tanh};
})();
// `/` of `Float`: by zero (either sign), the run-time error.
function floatDiv(a,b){
    if(b===0)throw new Error('division by zero');
    return a/b;
}
// The digits the Rust backend's `Display` writes: the shortest decimal that
// reads back as `x`, never with an exponent (`1`, `0.1`, `1e21` as
// `1000000000000000000000`, `-0`, `NaN`, `inf`).
function floatText(x){
    if(Number.isNaN(x))return 'NaN';
    if(x===Infinity)return 'inf';
    if(x===-Infinity)return '-inf';
    if(x===0)return Object.is(x,-0)?'-0':'0';
    const sign=x<0?'-':'',[m,e]=Math.abs(x).toExponential().split('e');
    let digits=m.replace('.','');const exp=Number(e);
    // Of two shortest digit strings exactly as near, JavaScript takes the
    // even one and Rust the larger: take the larger.
    const last=digits.charCodeAt(digits.length-1)-48;
    if(last%2===0&&last<9){
        const up=digits.slice(0,-1)+String(last+1);
        if(Number(up[0]+'.'+up.slice(1)+'e'+exp)===Math.abs(x)&&floatTie(Math.abs(x),BigInt(digits),exp-digits.length+1))digits=up;
    }
    if(exp>=digits.length-1)return sign+digits+'0'.repeat(exp-digits.length+1);
    if(exp<0)return sign+'0.'+'0'.repeat(-exp-1)+digits;
    return sign+digits.slice(0,exp+1)+'.'+digits.slice(exp+1);
}
// Whether `x` is exactly halfway between `d·10^p` and `(d+1)·10^p`.
function floatTie(x,d,p){
    const v=new DataView(new ArrayBuffer(8));v.setFloat64(0,x);
    const bits=v.getBigUint64(0),be=Number((bits>>52n)&0x7ffn);
    let m=bits&0xfffffffffffffn,e=be-1075;
    if(be===0)e=-1074;else m|=0x10000000000000n;
    // 2·m·2^e = (2d+1)·10^p, both sides scaled to integers.
    let l=2n*m,r=2n*d+1n;
    if(e>=0)l<<=BigInt(e);else r<<=BigInt(-e);
    if(p>=0)r*=10n**BigInt(p);else l*=10n**BigInt(-p);
    return l===r;
}
// `float_of_text`: a number as a literal writes one, with an optional `-`.
function floatOfText(t){
    return /^-?[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)?$/.test(t)?some(Number(t)):none();
}
function floatBuiltin(name,vs){
    const a=unref(vs[0]),b=unref(vs[1]);
    switch(name){
        case 'Float::of_i64':return Number(a);
        case 'I64::of_float':{
            const t=Math.trunc(a);
            if(!(t>=-9223372036854775808&&t<9223372036854775808))throw new Error('the number is too large');
            return BigInt(t);
        }
        case 'Float::of_text':return floatOfText(a);
        case 'Text::of_float':return floatText(a);
        case 'Float::bits':{if(a!==a)return 0x7ff8000000000000n;const v=new DataView(new ArrayBuffer(8));v.setFloat64(0,a);return v.getBigUint64(0);}
        case 'Float::of_bits':{const v=new DataView(new ArrayBuffer(8));v.setBigUint64(0,a);return v.getFloat64(0);}
        case 'Float::is_nan':return Number.isNaN(a);
        case 'Float::abs':return Math.abs(a);
        case 'Float::floor':return Math.floor(a);
        case 'Float::ceil':return Math.ceil(a);
        case 'Float::trunc':return Math.trunc(a);
        // Halves away from zero; `Math.round` takes them towards +∞.
        case 'Float::round':{
            if(!Number.isFinite(a))return a;
            const t=Math.trunc(a);
            return Math.abs(a-t)>=0.5?t+(a<0?-1:1):t;
        }
        case 'Float::sqrt':return Math.sqrt(a);
        case 'Float::cbrt':return floatMath.cbrt(a);
        case 'Float::exp':return floatMath.exp(a);
        case 'Float::ln':return floatMath.log(a);
        case 'Float::log2':return floatMath.log2(a);
        case 'Float::log10':return floatMath.log10(a);
        case 'Float::pow':return floatMath.pow(a,b);
        case 'Float::sin':return floatMath.sin(a);
        case 'Float::cos':return floatMath.cos(a);
        case 'Float::tan':return floatMath.tan(a);
        case 'Float::asin':return floatMath.asin(a);
        case 'Float::acos':return floatMath.acos(a);
        case 'Float::atan':return floatMath.atan(a);
        case 'Float::atan2':return floatMath.atan2(a,b);
        case 'Float::sinh':return floatMath.sinh(a);
        case 'Float::cosh':return floatMath.cosh(a);
        case 'Float::tanh':return floatMath.tanh(a);
        case 'Float::of_float32':return a;
    }
    throw new Error('unknown builtin '+name);
}
// `Float32` is a number too, always one `Math.fround` gives back: `+ - * /`
// and `sqrt` of two such, rounded once more by `Math.fround`, are IEEE 754's
// binary32 results (the binary64 result is never a double-rounding tie).
function float32Div(a,b){
    if(b===0)throw new Error('division by zero');
    return Math.fround(a/b);
}
function float32Builtin(name,vs){
    const a=unref(vs[0]),b=unref(vs[1]),f=Math.fround;
    switch(name){
        case 'Float32::of_float':return f(a);
        case 'Float32::bits':{if(a!==a)return 0x7fc00000n;const v=new DataView(new ArrayBuffer(4));v.setFloat32(0,a);return BigInt(v.getUint32(0));}
        case 'Float32::of_bits':{const v=new DataView(new ArrayBuffer(4));v.setUint32(0,Number(a));return v.getFloat32(0);}
        case 'Float32::is_nan':return Number.isNaN(a);
        case 'Float32::abs':return Math.abs(a);
        case 'Float32::floor':return Math.floor(a);
        case 'Float32::ceil':return Math.ceil(a);
        case 'Float32::trunc':return Math.trunc(a);
        case 'Float32::round':return floatBuiltin('Float::round',[a]);
        case 'Float32::sqrt':return f(Math.sqrt(a));
        case 'Float32::pow':return f(floatMath.pow(a,b));
        case 'Float32::atan2':return f(floatMath.atan2(a,b));
        default:return f(floatBuiltin('Float::'+name.slice(9),[a]));
    }
}
