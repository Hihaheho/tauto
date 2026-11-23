
function synDecode(answer,ctors){
    const b=new TextEncoder().encode(answer);let i=0;
    const num=()=>{while(b[i]===32)i++;let n=0;while(b[i]>=48&&b[i]<=57){n=n*10+(b[i]-48);i++;}return n;};
    const text=()=>{while(b[i]===32)i++;i++;const n=num();i++;const s=new TextDecoder().decode(b.subarray(i,i+n));i+=n;return s;};
    const value=()=>{
        switch(num()){
        case 0:{const d=ctors[num()],n=num(),fields=[],order=[];for(let k=0;k<n;k++){fields.push(value());order.push(k);}return construct(d[0],d[1],fields,order,d[2],d[3]);}
        case 1:return BigInt(num());
        case 2:return text();
        case 3:{const n=num(),items=[];for(let k=0;k<n;k++)items.push(value());return list(items);}
        case 4:return num()?some(value()):none();
        }
        throw new Error('tauto: the parser gave an unknown value');
    };
    const tag=num();
    if(tag===2)throw new Error('tauto: the tables of a syntax do not read');
    const v=value();
    return tag===0?ok(v):err(v);
}
