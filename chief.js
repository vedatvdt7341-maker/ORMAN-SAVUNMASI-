/* Kale Nöbeti · Ork Şefi: tek parça iskeletli deri (oyuna bağlanan modül) */
const CHF=(()=>{try{
const PI=Math.PI;
/* ---------- matematik ---------- */
const V=(x,y,z)=>[x,y,z],add=(a,b)=>[a[0]+b[0],a[1]+b[1],a[2]+b[2]],sub=(a,b)=>[a[0]-b[0],a[1]-b[1],a[2]-b[2]],mulS=(a,s)=>[a[0]*s,a[1]*s,a[2]*s],
dot=(a,b)=>a[0]*b[0]+a[1]*b[1]+a[2]*b[2],cross=(a,b)=>[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]],len=a=>Math.hypot(a[0],a[1],a[2]),nrm=a=>{const l=len(a)||1;return[a[0]/l,a[1]/l,a[2]/l]},lerp=(a,b,t)=>[a[0]+(b[0]-a[0])*t,a[1]+(b[1]-a[1])*t,a[2]+(b[2]-a[2])*t];
function mmul(a,b){const o=new Float32Array(16);for(let c=0;c<4;c++)for(let r=0;r<4;r++){let s=0;for(let k=0;k<4;k++)s+=a[k*4+r]*b[c*4+k];o[c*4+r]=s}return o}
function basis(x,y,z,t){return new Float32Array([x[0],x[1],x[2],0,y[0],y[1],y[2],0,z[0],z[1],z[2],0,t[0],t[1],t[2],1])}
function rotY(a){const c=Math.cos(a),s=Math.sin(a);return new Float32Array([c,0,-s,0,0,1,0,0,s,0,c,0,0,0,0,1])}
function persp(f,a,n,fr){const t=1/Math.tan(f/2);return new Float32Array([t/a,0,0,0,0,t,0,0,0,0,(fr+n)/(n-fr),-1,0,0,2*fr*n/(n-fr),0])}
function look(e,c,u){const z=nrm(sub(e,c)),x=nrm(cross(u,z)),y=cross(z,x);return new Float32Array([x[0],y[0],z[0],0,x[1],y[1],z[1],0,x[2],y[2],z[2],0,-dot(x,e),-dot(y,e),-dot(z,e),1])}
function nmat(m){const a=m[0],b=m[1],c=m[2],d=m[4],e=m[5],f=m[6],g=m[8],h=m[9],i=m[10],A=e*i-f*h,B=-(d*i-f*g),C=d*h-e*g,det=a*A+b*B+c*C||1e-9;
 return new Float32Array([A/det,B/det,C/det,-(b*i-c*h)/det,(a*i-c*g)/det,-(a*h-b*g)/det,(b*f-c*e)/det,-(a*f-c*d)/det,(a*e-b*d)/det])}
const hx=s=>{s=s.replace('#','');return[parseInt(s.slice(0,2),16)/255,parseInt(s.slice(2,4),16)/255,parseInt(s.slice(4,6),16)/255]};
/* ---------- geometri ---------- */
function mk(v,nv,ix){const g={n:ix.length,cv:v,cn:nv,ci:ix};g.vao=gl.createVertexArray();gl.bindVertexArray(g.vao);g.vb=gl.createBuffer();gl.bindBuffer(gl.ARRAY_BUFFER,g.vb);gl.bufferData(gl.ARRAY_BUFFER,new Float32Array(v),gl.STATIC_DRAW);gl.enableVertexAttribArray(0);gl.vertexAttribPointer(0,3,gl.FLOAT,false,0,0);g.nb=gl.createBuffer();gl.bindBuffer(gl.ARRAY_BUFFER,g.nb);gl.bufferData(gl.ARRAY_BUFFER,new Float32Array(nv),gl.STATIC_DRAW);gl.enableVertexAttribArray(1);gl.vertexAttribPointer(1,3,gl.FLOAT,false,0,0);g.ib=gl.createBuffer();gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER,g.ib);gl.bufferData(gl.ELEMENT_ARRAY_BUFFER,new Uint16Array(ix),gl.STATIC_DRAW);gl.bindVertexArray(null);return g}
function sphG(sg,rg){const v=[],n=[],ix=[];for(let j=0;j<=rg;j++){const t=j/rg*PI;for(let i=0;i<=sg;i++){const a=i/sg*PI*2,x=Math.sin(t)*Math.cos(a),y=Math.cos(t),z=Math.sin(t)*Math.sin(a);v.push(x,y,z);n.push(x,y,z)}}for(let j=0;j<rg;j++)for(let i=0;i<sg;i++){const a=j*(sg+1)+i,b=a+sg+1;ix.push(a,a+1,b,a+1,b+1,b)}return mk(v,n,ix)}
const CY={};function cylG(r){r=Math.round(r*20)/20;if(CY[r])return CY[r];const sg=18,v=[],n=[],ix=[],sl=1-r,l=Math.hypot(1,sl);for(let i=0;i<=sg;i++){const a=i/sg*PI*2,c=Math.cos(a),s=Math.sin(a);v.push(c,0,s,c*r,1,s*r);n.push(c/l,sl/l,s/l,c/l,sl/l,s/l)}for(let i=0;i<sg;i++){const a=i*2;ix.push(a,a+2,a+1,a+1,a+2,a+3)}
 for(const[y,rr,ny]of[[0,1,-1],[1,r,1]]){if(rr<=0)continue;const b=v.length/3;v.push(0,y,0);n.push(0,ny,0);for(let i=0;i<=sg;i++){const a=i/sg*PI*2;v.push(Math.cos(a)*rr,y,Math.sin(a)*rr);n.push(0,ny,0)}for(let i=0;i<sg;i++)ix.push(b,b+1+i,b+2+i)}return CY[r]=mk(v,n,ix)}
function boxG(){const v=[],n=[],ix=[],F=[[[0,0,1],[1,0,0],[0,1,0]],[[0,0,-1],[-1,0,0],[0,1,0]],[[1,0,0],[0,0,-1],[0,1,0]],[[-1,0,0],[0,0,1],[0,1,0]],[[0,1,0],[1,0,0],[0,0,-1]],[[0,-1,0],[1,0,0],[0,0,1]]];for(const[f,u,w]of F){const b=v.length/3;for(const[a,c]of[[-1,-1],[1,-1],[1,1],[-1,1]]){v.push((f[0]+u[0]*a+w[0]*c)*.5,(f[1]+u[1]*a+w[1]*c)*.5,(f[2]+u[2]*a+w[2]*c)*.5);n.push(...f)}ix.push(b,b+1,b+2,b,b+2,b+3)}return mk(v,n,ix)}
const GS=sphG(24,16),GB=boxG();
/* ---------- çizim listesi ---------- */
let L=[];
const it=(g,M,c,o)=>L.push({g,M,c:typeof c=='string'?hx(c):c,e:o&&o.em||0,m:o&&o.met||0});
function frame(y,ref){y=nrm(y);let r=Math.abs(dot(y,ref))>.95?[1,0,0]:ref;const x=nrm(cross(r,y)),z=cross(x,y);return[x,z]}
function sp(p,r,c,o){const R=o&&o.R;if(R){const[x,y,z]=R;it(GS,basis(mulS(x,r[0]),mulS(y,r[1]),mulS(z,r[2]),p),c,o)}else it(GS,basis([r[0],0,0],[0,r[1],0],[0,0,r[2]],p),c,o)}
function seg(A,B,r1,r2,c,o){const d=sub(B,A),l=len(d)||1e-4,y=mulS(d,1/l),[x,z]=frame(y,[0,0,1]),rz=o&&o.rz||1;it(cylG(r1>0?r2/r1:1),basis(mulS(x,r1),d,mulS(z,r1*rz),A),c,o);if(!(o&&o.nocap)){if(r1>.004)sp(A,[r1,r1,r1*rz],c,o);if(r2>.004)sp(B,[r2,r2,r2*rz],c,o)}}
function ellOn(A,B,t,rx,lf,rz,c,o){const d=sub(B,A),l=len(d)||1e-4,y=mulS(d,1/l),[x,z]=frame(y,[0,0,1]),off=o&&o.off||[0,0,0];sp(add(add(A,mulS(d,t)),off),[rx,l*lf,rz],c,Object.assign({R:[x,y,z]},o))}
function cone(A,B,r,c,o){const d=sub(B,A),y=nrm(d),[x,z]=frame(y,[0,0,1]);it(cylG(0),basis(mulS(x,r),d,mulS(z,r),A),c,o)}
function box(p,s,c,o){const R=o&&o.R||[[1,0,0],[0,1,0],[0,0,1]];it(GB,basis(mulS(R[0],s[0]),mulS(R[1],s[1]),mulS(R[2],s[2]),p),c,o)}
function disc(p,ax,r,th,c,o){seg(sub(p,mulS(ax,th)),add(p,mulS(ax,th)),r,r,c,Object.assign({nocap:1},o))}
const rx=(v,a)=>[v[0],v[1]*Math.cos(a)-v[2]*Math.sin(a),v[1]*Math.sin(a)+v[2]*Math.cos(a)];
/* --- SDF yardımcıları --- */
function sdEll(q,r){const a=[q[0]/r[0],q[1]/r[1],q[2]/r[2]],b=[q[0]/(r[0]*r[0]),q[1]/(r[1]*r[1]),q[2]/(r[2]*r[2])],k0=len(a),k1=len(b)||1e-6;return k0*(k0-1)/k1}
function sdRC(p,a,b,r1,r2){const ba=sub(b,a),l2=dot(ba,ba),rr=r1-r2,a2=l2-rr*rr,il2=1/l2,pa=sub(p,a),y=dot(pa,ba),z=y-l2,xv=sub(mulS(pa,l2),mulS(ba,y)),x2=dot(xv,xv),y2=y*y*l2,z2=z*z*l2,k=Math.sign(rr)*rr*rr*x2;
 if(Math.sign(z)*a2*z2>k)return Math.sqrt(x2+z2)*il2-r2;if(Math.sign(y)*a2*y2<k)return Math.sqrt(x2+y2)*il2-r1;return(Math.sqrt(x2*a2*il2)+y*rr)*il2-r1}
const smin=(a,b,k)=>{const h=Math.max(k-Math.abs(a-b),0)/k;return Math.min(a,b)-h*h*k*.25};
/* --- iskelet (H=1 birim, dinlenme pozu) --- */
const J=[[0,.455,0],[0,.6,0],[0,.75,.005],[0,.8,.03]];const PAR=[-1,0,1,2];
for(const s of[-1,1]){}
// 4/5 üst kol, 6/7 ön kol, 8/9 el, 10/11 uyluk, 12/13 baldır, 14/15 ayak  (çift = sol, tek = sağ)
const SH=s=>[s*.198,.712,-.005],EL=s=>[s*.262,.555,-.012],WR=s=>[s*.292,.405,.012],HP=s=>[s*.076,.445,0],KN=s=>[s*.084,.245,.012],AN=s=>[s*.088,.058,-.004];
for(const[f,p]of[[SH,1],[EL,null],[WR,null],[HP,0],[KN,null],[AN,null]]){}
J[4]=SH(-1);J[5]=SH(1);J[6]=EL(-1);J[7]=EL(1);J[8]=WR(-1);J[9]=WR(1);J[10]=HP(-1);J[11]=HP(1);J[12]=KN(-1);J[13]=KN(1);J[14]=AN(-1);J[15]=AN(1);
PAR[4]=1;PAR[5]=1;PAR[6]=4;PAR[7]=5;PAR[8]=6;PAR[9]=7;PAR[10]=0;PAR[11]=0;PAR[12]=10;PAR[13]=11;PAR[14]=12;PAR[15]=13;
const NB=16,bi=(s,base)=>base+(s>0?1:0),TIPS={},TOES={};
/* --- vücut primitifleri --- */
const PR=[];// {t:'e'|'c', ...,b:kemik,k:yumuşaklık, sub:çıkarma}
function E(c,r,b,k,ax,sub){const R=ax||[[1,0,0],[0,1,0],[0,0,1]];PR.push({t:'e',c,r,R,b,k,sub})}
function Cc(a,bb,r1,r2,b,k,sub){PR.push({t:'c',a,b2:bb,r1,r2,b,k,sub})}
function Ealong(A,B,t,rx,ry,rz,off,b,k){const d=nrm(sub(B,A)),[x,z]=frame(d,[0,0,1]);E(add(lerp(A,B,t),off),[rx,ry,rz],b,k,[x,d,z])}
// gövde
E([0,.462,0],[.128,.07,.098],0,.035);
E([0,.535,.008],[.118,.085,.09],0,.03);
E([0,.635,-.004],[.175,.112,.112],1,.034);
E([0,.655,-.07],[.15,.1,.05],1,.025);
for(const s of[-1,1]){
 E([s*.074,.664,.076],[.088,.054,.05],1,.02,[[1,0,0],nrm([0,1,.25]),nrm([0,-.25,1])]);
 E([s*.134,.625,-.012],[.07,.104,.08],1,.026);
 E([s*.1,.53,.036],[.047,.072,.066],0,.02);
 E([s*.07,.736,-.012],[.1,.046,.068],1,.034);
 for(let r=0;r<3;r++)E([s*.032,.592-r*.038,.086-r*.002],[.032,.018,.024],r<1?1:0,.011);
 // kollar
 const S=SH(s),El=EL(s),W=WR(s),ua=bi(s,4),fa=bi(s,6),hd=bi(s,8);
 E(add(S,[s*.014,.006,0]),[.072,.064,.068],ua,.026);
 Cc(S,El,.046,.036,ua,.02);
 Ealong(S,El,.48,.048,.078,.047,[0,0,.024],ua,.016);
 Ealong(S,El,.42,.044,.082,.042,[0,0,-.024],ua,.016);
 Cc(El,W,.038,.025,fa,.016);
 Ealong(El,W,.28,.05,.072,.046,[s*.005,0,.009],fa,.016);
 // avuç, bilek, parmak boğumları
 Cc(add(W,[0,.01,0]),add(W,[0,-.02,.002]),.026,.024,hd,.012);
 E(add(W,[s*.002,-.036,.002]),[.027,.034,.016],hd,.01);
 E(add(W,[-s*.006,-.03,.014]),[.014,.02,.01],hd,.008);
 const grip=s>0;TIPS[s]=[];
 for(let i=0;i<4;i++){const z=-.016+i*.0105,lenF=[.92,1,.97,.82][i],rr=[.0078,.0082,.0078,.007][i];let p=add(W,[s*.003,-.062,z]);E(p,[.009,.008,.0085],hd,.004);
  let d=[0,-1,0];const segL=[.02,.015,.012].map(x=>x*lenF);
  for(let k=0;k<3;k++){d=grip?nrm(add(d,[-s*.75,.18,0])):nrm(add(d,[0,.0,.22]));const n=add(p,mulS(d,segL[k]));Cc(p,n,rr*(1-k*.12),rr*(.92-k*.14),hd,.003);if(k<2)E(n,[rr*1.05,rr*1.05,rr*1.05],hd,.002);p=n}
  TIPS[s].push([p,d])}
 {let p=add(W,[-s*.002,-.03,.02]);let d=nrm([-s*.1,-.6,.7]);for(let k=0;k<2;k++){if(grip)d=nrm(add(d,[-s*.5,-.1,-.3]));const n=add(p,mulS(d,.018-k*.004));Cc(p,n,.0105-k*.0015,.0092-k*.002,hd,.004);p=n}TIPS[s].push([p,d])}
 // bacaklar
 const Hp=HP(s),K=KN(s),A=AN(s),th=bi(s,10),cf=bi(s,12),ft=bi(s,14);
 Cc(Hp,K,.051,.035,th,.024);
 Ealong(Hp,K,.44,.05,.1,.046,[s*.006,0,.03],th,.011);
 Ealong(Hp,K,.62,.04,.075,.037,[s*.027,0,.014],th,.009);
 Ealong(Hp,K,.76,.034,.058,.032,[-s*.02,0,.02],th,.008);
 Ealong(Hp,K,.42,.047,.095,.042,[0,0,-.024],th,.011);
 Ealong(Hp,K,.3,.033,.08,.032,[-s*.03,0,0],th,.009);
 E(add(K,[0,.004,.024]),[.025,.027,.017],cf,.01);
 Cc(K,A,.031,.02,cf,.011);
 Ealong(K,A,.27,.039,.07,.035,[s*.013,0,-.021],cf,.009);
 Ealong(K,A,.25,.041,.074,.037,[-s*.012,0,-.023],cf,.009);
 Ealong(K,A,.45,.024,.09,.024,[s*.019,0,.012],cf,.007);
 E(add(A,[0,-.024,.029]),[.031,.021,.058],ft,.015);
 E(add(A,[0,-.03,-.018]),[.026,.024,.03],ft,.012);
 for(const e of[-1,1])E(add(A,[e*.026,.004,0]),[.009,.012,.011],cf,.008);
 E(add(A,[-s*.006,-.036,.066]),[.032,.013,.028],ft,.011);TOES[s]=[];
 for(let i=0;i<5;i++){const x=-s*.022+s*i*.011,big=i==0,r=big?.0105:.008-i*.0006,b0=add(A,[x,-.038,.083-i*.004]),tip=add(b0,[s*.002,-.004,big?.025:.02-i*.002]);Cc(b0,tip,r,r*.92,ft,.004);TOES[s].push([tip,r])}
}
// boyun + baş
Cc([0,.71,-.005],[0,.79,.02],.047,.042,2,.03);
const HC=J[3];
E(add(HC,[0,.022,0]),[.094,.094,.092],3,.02);
E(add(HC,[0,-.042,.024]),[.1,.05,.07],3,.02);
E(add(HC,[0,-.074,.074]),[.036,.024,.026],3,.012);
E(add(HC,[0,.02,.078]),[.08,.017,.026],3,.01);
for(const s of[-1,1]){E(add(HC,[s*.052,-.012,.066]),[.032,.024,.028],3,.012);Cc(add(HC,[s*.084,.006,-.004]),add(HC,[s*.15,.05,-.04]),.026,.006,3,.012);E(add(HC,[s*.036,.0,.088]),[.022,.017,.018],3,.006,null,1)}
E(add(HC,[0,-.012,.096]),[.022,.021,.021],3,.01);
E(add(HC,[0,-.052,.096]),[.036,.0055,.02],3,.004,null,1);
for(const s of[-1,1]){
 E(add(HC,[s*.036,.016,.088]),[.026,.009,.016],3,.004);
 E(add(HC,[s*.036,-.014,.086]),[.022,.0075,.013],3,.004);
 E(add(HC,[s*.06,-.006,.07]),[.03,.022,.026],3,.01);
 E(add(HC,[s*.072,-.042,.045]),[.026,.032,.03],3,.012);
 E(add(HC,[s*.017,-.02,.099]),[.0115,.01,.0105],3,.004);
 E(add(HC,[s*.0095,-.025,.106]),[.005,.0045,.006],3,.002,null,1);
 E(add(HC,[s*.034,-.036,.094]),[.0045,.019,.007],3,.003,[nrm([1,-s*.35,0]),nrm([s*.35,1,0]),[0,0,1]],1);
 Cc(add(HC,[s*.098,.004,.004]),add(HC,[s*.14,.042,-.032]),.012,.004,3,.004,1);
 E(add(HC,[s*.09,-.028,-.004]),[.009,.012,.009],3,.006);
 Cc(add(HC,[s*.05,-.06,-.01]),[s*.028,.718,.05],.011,.009,2,.012);
 Cc([s*.02,.716,.075],[s*.15,.726,.022],.0095,.009,1,.01);
 for(const y of[.046,.058])E(add(HC,[s*.03,y,.086]),[.026,.0022,.007],3,.002,null,1);
}
Cc(add(HC,[0,.016,.094]),add(HC,[0,-.012,.107]),.0095,.013,3,.006);
E(add(HC,[0,.022,.1]),[.0035,.013,.01],3,.003,null,1);
E(add(HC,[0,-.045,.101]),[.034,.0085,.012],3,.004);
E(add(HC,[0,-.06,.098]),[.029,.0095,.013],3,.004);
E(add(HC,[0,-.08,.1]),[.003,.011,.007],3,.002,null,1);
for(const p of PR){let lo,hi,m=(p.k||0)+.02;if(p.t=='e'){const r=Math.max(...p.r);lo=sub(p.c,[r,r,r]);hi=add(p.c,[r,r,r])}else{const r=Math.max(p.r1,p.r2);lo=[Math.min(p.a[0],p.b2[0])-r,Math.min(p.a[1],p.b2[1])-r,Math.min(p.a[2],p.b2[2])-r];hi=[Math.max(p.a[0],p.b2[0])+r,Math.max(p.a[1],p.b2[1])+r,Math.max(p.a[2],p.b2[2])+r]}p.lo=sub(lo,[m,m,m]);p.hi=add(hi,[m,m,m])}
function pd(p,q){if(p.t=='e'){const d=sub(q,p.c),R=p.R;return sdEll([dot(d,R[0]),dot(d,R[1]),dot(d,R[2])],p.r)}return sdRC(q,p.a,p.b2,p.r1,p.r2)}
const inB=(p,q)=>q[0]>=p.lo[0]&&q[0]<=p.hi[0]&&q[1]>=p.lo[1]&&q[1]<=p.hi[1]&&q[2]>=p.lo[2]&&q[2]<=p.hi[2];
function sdf(q){let d=1e9;for(const p of PR)if(!p.sub&&inB(p,q))d=smin(d,pd(p,q),p.k);for(const p of PR)if(p.sub&&inB(p,q))d=-smin(-d,pd(p,q),p.k);return d}
/* --- yüzey ağları (surface nets) --- */
function buildMesh(){const h=.0068,X0=-.42,Y0=-.01,Z0=-.2,nx=Math.ceil(.84/h)+1,ny=Math.ceil(1.0/h)+1,nz=Math.ceil(.42/h)+1,F=new Float32Array(nx*ny*nz).fill(1e9),I=(i,j,k)=>(k*ny+j)*nx+i;
 for(const p of PR){if(p.sub)continue;const i0=Math.max(0,Math.floor((p.lo[0]-X0)/h)),i1=Math.min(nx-1,Math.ceil((p.hi[0]-X0)/h)),j0=Math.max(0,Math.floor((p.lo[1]-Y0)/h)),j1=Math.min(ny-1,Math.ceil((p.hi[1]-Y0)/h)),k0=Math.max(0,Math.floor((p.lo[2]-Z0)/h)),k1=Math.min(nz-1,Math.ceil((p.hi[2]-Z0)/h));
  for(let k=k0;k<=k1;k++)for(let j=j0;j<=j1;j++)for(let i=i0;i<=i1;i++){const q=[X0+i*h,Y0+j*h,Z0+k*h],ix=I(i,j,k);F[ix]=smin(F[ix],pd(p,q),p.k)}}
 for(const p of PR){if(!p.sub)continue;const i0=Math.max(0,Math.floor((p.lo[0]-X0)/h)),i1=Math.min(nx-1,Math.ceil((p.hi[0]-X0)/h)),j0=Math.max(0,Math.floor((p.lo[1]-Y0)/h)),j1=Math.min(ny-1,Math.ceil((p.hi[1]-Y0)/h)),k0=Math.max(0,Math.floor((p.lo[2]-Z0)/h)),k1=Math.min(nz-1,Math.ceil((p.hi[2]-Z0)/h));
  for(let k=k0;k<=k1;k++)for(let j=j0;j<=j1;j++)for(let i=i0;i<=i1;i++){const q=[X0+i*h,Y0+j*h,Z0+k*h],ix=I(i,j,k);F[ix]=-smin(-F[ix],pd(p,q),p.k)}}
 const VI=new Int32Array(nx*ny*nz).fill(-1),P=[];
 const ED=[[0,1],[2,3],[4,5],[6,7],[0,2],[1,3],[4,6],[5,7],[0,4],[1,5],[2,6],[3,7]],CO=[[0,0,0],[1,0,0],[0,1,0],[1,1,0],[0,0,1],[1,0,1],[0,1,1],[1,1,1]];
 for(let k=0;k<nz-1;k++)for(let j=0;j<ny-1;j++)for(let i=0;i<nx-1;i++){const v=CO.map(o=>F[I(i+o[0],j+o[1],k+o[2])]);let neg=0;for(const a of v)if(a<0)neg++;if(neg==0||neg==8)continue;
  let sx=0,sy=0,sz=0,c=0;for(const[a,b]of ED){const va=v[a],vb=v[b];if((va<0)!=(vb<0)){const t=va/(va-vb),A=CO[a],B=CO[b];sx+=A[0]+(B[0]-A[0])*t;sy+=A[1]+(B[1]-A[1])*t;sz+=A[2]+(B[2]-A[2])*t;c++}}
  VI[I(i,j,k)]=P.length/3;P.push(X0+(i+sx/c)*h,Y0+(j+sy/c)*h,Z0+(k+sz/c)*h)}
 const IX=[];const q4=(a,b,c,d,flip)=>{if(a<0||b<0||c<0||d<0)return;if(flip)IX.push(a,c,b,a,d,c);else IX.push(a,b,c,a,c,d)};
 for(let k=1;k<nz-1;k++)for(let j=1;j<ny-1;j++)for(let i=1;i<nx-1;i++){const f0=F[I(i,j,k)]<0;
  if(f0!=(F[I(i+1,j,k)]<0))q4(VI[I(i,j-1,k-1)],VI[I(i,j,k-1)],VI[I(i,j,k)],VI[I(i,j-1,k)],!f0);
  if(f0!=(F[I(i,j+1,k)]<0))q4(VI[I(i-1,j,k-1)],VI[I(i-1,j,k)],VI[I(i,j,k)],VI[I(i,j,k-1)],!f0);
  if(f0!=(F[I(i,j,k+1)]<0))q4(VI[I(i-1,j-1,k)],VI[I(i,j-1,k)],VI[I(i,j,k)],VI[I(i-1,j,k)],!f0)}
 const nv=P.length/3,N=new Float32Array(nv*3),Cl=new Float32Array(nv*3),AM=new Float32Array(nv*2),BI=new Float32Array(nv*4),BW=new Float32Array(nv*4),e=.003;
 const SKC=hx('#356b44'),PAN=hx('#2f2518'),BOOT=hx('#3a2412');
 for(let v=0;v<nv;v++){const q=[P[v*3],P[v*3+1],P[v*3+2]];
  const g=nrm([sdf(add(q,[e,0,0]))-sdf(sub(q,[e,0,0])),sdf(add(q,[0,e,0]))-sdf(sub(q,[0,e,0])),sdf(add(q,[0,0,e]))-sdf(sub(q,[0,0,e]))]);N.set(g,v*3);
  let ao=0;for(const[dd,w]of[[.008,.6],[.02,.35],[.045,.2]]){ao+=w*Math.max(0,dd-sdf(add(q,mulS(g,dd))))/dd}AM[v*2]=Math.max(.25,1-ao*.9);
  const bw=new Float32Array(NB);let dmin=1e9;const ds=[];for(const p of PR){if(p.sub||!inB(p,q))continue;const d=pd(p,q);ds.push([p.b,d]);dmin=Math.min(dmin,d)}for(const[b,d]of ds)bw[b]+=Math.exp(-Math.max(0,d-dmin)/.011);
  const ord=[...bw.keys()].sort((a,b)=>bw[b]-bw[a]).slice(0,4);let tw=0;for(const o of ord)tw+=bw[o];for(let n=0;n<4;n++){BI[v*4+n]=ord[n];BW[v*4+n]=tw?bw[ord[n]]/tw:(n?0:1)}
  const ax=Math.abs(q[0]);let col=SKC,mat=1;if(q[1]<.445&&q[1]>.088&&!(ax>.2&&q[1]>.3)){col=PAN;mat=0}
  Cl.set(col,v*3);AM[v*2+1]=mat}
 return{P:new Float32Array(P),N,Cl,AM,BI,BW,IX:new Uint32Array(IX),nv,ni:IX.length}}
const tB=performance.now();const MESH=buildMesh();const buildMs=Math.round(performance.now()-tB);
/* --- kavisli satır geometrisi --- */
const BLADE=(()=>{const Lb=.215,th=.0065,N=28,sp_=[],ed=[];for(let i=0;i<=N;i++){const a=i/N,y=a*Lb,c=.05*a*a,w=.1+.06*a-.02*a*a;sp_.push([c-.012,y]);ed.push([c+w,y+.02*Math.sin(a*PI)])}
 const tip=[];const tc=[(sp_[N][0]+ed[N][0])/2,Lb],tr=(ed[N][0]-sp_[N][0])/2;for(let i=1;i<10;i++){const q=i/10*PI;tip.push([tc[0]+Math.cos(q)*tr,tc[1]+Math.sin(q)*tr*.55])}
 const out=[...sp_.slice().reverse().map(p=>p),...[]];const poly=[[sp_[0][0],0],...ed,...tip,...sp_.slice().reverse()];
 const cx=poly.reduce((a,p)=>a+p[0],0)/poly.length,cy=poly.reduce((a,p)=>a+p[1],0)/poly.length;
 function extrude(pts,z0,z1,closed){const v=[],n=[],ix=[];for(const[zz,nz]of[[z1,1],[z0,-1]]){const b=v.length/3;v.push(cx,cy,zz);n.push(0,0,nz);for(const p of pts){v.push(p[0],p[1],zz);n.push(0,0,nz)}for(let i=0;i<pts.length;i++){const a=b+1+i,c=b+1+(i+1)%pts.length;if(nz>0)ix.push(b,a,c);else ix.push(b,c,a)}}
  for(let i=0;i<pts.length;i++){const p=pts[i],q=pts[(i+1)%pts.length],dx=q[0]-p[0],dy=q[1]-p[1],l=Math.hypot(dx,dy)||1,nx=dy/l,ny=-dx/l,b=v.length/3;v.push(p[0],p[1],z0,q[0],q[1],z0,q[0],q[1],z1,p[0],p[1],z1);for(let k=0;k<4;k++)n.push(nx,ny,0);ix.push(b,b+1,b+2,b,b+2,b+3)}return mk(v,n,ix)}
 const body=extrude(poly,-th,th);
 const band=[];for(const p of ed)band.push(p);for(const p of tip)band.push(p);const inner=band.map(p=>[p[0]-(p[0]-cx)*.12,p[1]-(p[1]-cy)*.08]);
 const v=[],n=[],ix=[];for(let i=0;i<band.length;i++){const p=band[i],q=inner[i];v.push(p[0],p[1],0,q[0],q[1],th*1.15,q[0],q[1],-th*1.15);n.push(1,0,0,0,0,1,0,0,-1)}for(let i=0;i<band.length-1;i++){const a=i*3,b=(i+1)*3;ix.push(a,b,a+1,b,b+1,a+1,a,a+2,b,b,a+2,b+2)}
 const edge=mk(v,n,ix);return{body,edge}})();
/* --- tek parça pelerin (her karede güncellenir) --- */
const CAPE=(()=>{const nu=18,nv=26,ix=[];for(let j=0;j<nv-1;j++)for(let i=0;i<nu-1;i++){const a=j*nu+i;ix.push(a,a+1,a+nu,a+1,a+nu+1,a+nu)}const g={nu,nv,n:ix.length,vao:gl.createVertexArray(),vb:gl.createBuffer(),nb:gl.createBuffer(),ib:gl.createBuffer(),P:new Float32Array(nu*nv*3),N:new Float32Array(nu*nv*3)};gl.bindVertexArray(g.vao);gl.bindBuffer(gl.ARRAY_BUFFER,g.vb);gl.bufferData(gl.ARRAY_BUFFER,g.P,gl.DYNAMIC_DRAW);gl.enableVertexAttribArray(0);gl.vertexAttribPointer(0,3,gl.FLOAT,false,0,0);gl.bindBuffer(gl.ARRAY_BUFFER,g.nb);gl.bufferData(gl.ARRAY_BUFFER,g.N,gl.DYNAMIC_DRAW);gl.enableVertexAttribArray(1);gl.vertexAttribPointer(1,3,gl.FLOAT,false,0,0);gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER,g.ib);gl.bufferData(gl.ELEMENT_ARRAY_BUFFER,new Uint16Array(ix),gl.STATIC_DRAW);gl.bindVertexArray(null);return g})();
const CAPE2=(()=>{const nu=32,nv=32,ix=[],hs=n=>{const v=Math.sin(n*127.1+19.7)*43758.5453;return v-Math.floor(v)};
 // alt kenar: farklı uzunlukta yırtık şeritler ve V çentikler
 const jm=[];for(let i=0;i<nu;i++){const strip=Math.pow(hs(Math.floor(i/2)+9),1.3)*.34,fine=hs(i*1.7)*.1,notch=Math.max(0,.2-Math.abs(i-nu*.3)*.05)+Math.max(0,.26-Math.abs(i-nu*.68)*.06)+Math.max(0,.14-Math.abs(i-nu*.08)*.06);jm[i]=Math.round((1-Math.min(.55,strip+fine+notch))*(nv-1))}
 const cuts=[7,13,19,24,28].map((c,k)=>({c,top:Math.round(nv*(.45+hs(k+3)*.25))}));
 for(let j=0;j<nv-1;j++)for(let i=0;i<nu-1;i++){if(j>=jm[i]&&j>=jm[i+1])continue;
  const hole=j>nv*.38&&j<Math.min(jm[i],jm[i+1])-1&&(hs(Math.floor(i/2)*13.3+Math.floor(j/2)*7.1)<.11||hs(Math.floor(i/3)*5.1+Math.floor(j/3)*9.7)<.05);if(hole)continue;
  if(cuts.some(q=>q.c==i&&j>=q.top))continue;
  const a=j*nu+i;if(j<jm[i]&&j<jm[i+1])ix.push(a,a+1,a+nu,a+1,a+nu+1,a+nu);else if(j<jm[i])ix.push(a,a+1,a+nu);else ix.push(a,a+1,a+nu+1)}
 const g={nu,nv,n:ix.length,vao:gl.createVertexArray(),vb:gl.createBuffer(),nb:gl.createBuffer(),ib:gl.createBuffer(),P:new Float32Array(nu*nv*3),N:new Float32Array(nu*nv*3)};gl.bindVertexArray(g.vao);gl.bindBuffer(gl.ARRAY_BUFFER,g.vb);gl.bufferData(gl.ARRAY_BUFFER,g.P,gl.DYNAMIC_DRAW);gl.enableVertexAttribArray(0);gl.vertexAttribPointer(0,3,gl.FLOAT,false,0,0);gl.bindBuffer(gl.ARRAY_BUFFER,g.nb);gl.bufferData(gl.ARRAY_BUFFER,g.N,gl.DYNAMIC_DRAW);gl.enableVertexAttribArray(1);gl.vertexAttribPointer(1,3,gl.FLOAT,false,0,0);gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER,g.ib);gl.bufferData(gl.ELEMENT_ARRAY_BUFFER,new Uint16Array(ix),gl.STATIC_DRAW);gl.bindVertexArray(null);return g})();
function capeUpdate(t,walking){const{nu,nv,P,N}=CAPE2,amp=walking?1:.5;for(let j=0;j<nv;j++)for(let i=0;i<nu;i++){const u=i/(nu-1)*2-1,v=j/(nv-1),hw=.17+.15*v,y=.728-v*.66,wave=Math.sin(u*3.5+t*3.3+v*4.8)*.0672*v*amp+Math.sin(u*7.5-t*4.3+v*7.5)*.0208*v*amp+Math.sin(u*2-t*2.1+v*2.5)*.032*v*v*amp,bil=(Math.sin(t*2.7-v*5.5+u*.8)*.5+.5)*.12*v*v*amp,z=-.05-(1-u*u)*(.045+.02*v)-v*.17-v*v*.04+wave-bil,x=u*hw*(1+.192*v*Math.sin(t*2.3-v*4))+Math.sin(t*1.9+v*3.2)*.0384*v*amp;P.set([x,y+bil*.35,z],(j*nu+i)*3)}
 for(let j=0;j<nv;j++)for(let i=0;i<nu;i++){const g=(a,b)=>{a=Math.max(0,Math.min(nu-1,a));b=Math.max(0,Math.min(nv-1,b));const k=(b*nu+a)*3;return[P[k],P[k+1],P[k+2]]},du=sub(g(i+1,j),g(i-1,j)),dv=sub(g(i,j+1),g(i,j-1));N.set(nrm(cross(dv,du)),(j*nu+i)*3)}
 gl.bindBuffer(gl.ARRAY_BUFFER,CAPE2.vb);gl.bufferSubData(gl.ARRAY_BUFFER,0,P);gl.bindBuffer(gl.ARRAY_BUFFER,CAPE2.nb);gl.bufferSubData(gl.ARRAY_BUFFER,0,N)}
/* --- sert parçalar (kemiğe bağlı) --- */
const RG=[];const rg=(b,fn)=>{const save=L;L=[];fn();for(const d of L)RG.push(Object.assign(d,{b}));L=save};
(()=>{const GOLD='#c99a3a',HC2=J[3];
 // göz, diş
 rg(3,()=>{for(const s of[-1,1]){const E0=add(HC2,[s*.036,.0,.08]);sp(E0,[.016,.012,.01],'#1a0a06');sp(add(E0,[0,0,.007]),[.011,.008,.006],'#ffb020',{em:.9});sp(add(E0,[s*.001,0,.012]),[.004,.006,.003],'#120806');
   const tb=add(HC2,[s*.03,-.058,.088]);cone(tb,add(tb,[s*.008,.05,.006]),.0085,'#e8dcc0');L[L.length-1].v0=1;cone(add(HC2,[s*.017,-.054,.093]),add(HC2,[s*.018,-.064,.094]),.004,'#e8dcc0');L[L.length-1].v0=1;
   for(const z of[0,1])seg(add(HC2,[s*.093,-.002-z*.01,-.006]),add(HC2,[s*.093,-.009-z*.01,-.006]),.008,.008,GOLD,{met:1,nocap:1})}
  for(let i=-2;i<=2;i++)cone(add(HC2,[i*.009,-.049,.099]),add(HC2,[i*.009,-.058,.1]),.0035,'#e8dcc0');
  const n0=L.length;const tk=add(HC2,[0,.105,-.012]);sp(tk,[.026,.022,.026],'#16120f');seg(tk,add(tk,[0,.035,-.03]),.014,.008,'#16120f');seg(add(tk,[0,.035,-.03]),add(tk,[0,-.07,-.09]),.009,.005,'#16120f');seg(add(tk,[0,-.004,0]),add(tk,[0,.008,0]),.022,.022,GOLD,{met:1,nocap:1});
  box(add(HC2,[.042,.025,.088]),[.004,.06,.003],'#c9a090',{R:[nrm([1,.4,0]),nrm([-.4,1,0]),[0,0,1]]});for(let k=n0;k<L.length;k++)L[k].v0=1;
  /* ---- demir miğfer (yalnız yeni sürüm) ---- */
  const h0=L.length,IRON='#2a2c31',IRD='#151618',RIV='#5e6064',C=add(HC2,[0,.026,-.002]),ra=.109,rb=.104,rc=.11;
  const rimY=th=>{const f=Math.cos(th),ax=Math.abs(Math.atan2(Math.sin(th),Math.cos(th)));let y=f>0?-.008+.034*f:-.008+.05*f;// arka daha aşağı
   if(f>0){const vb=Math.max(0,1-ax/.3);y+=-.03*vb*vb*(3-2*vb)+.006*Math.max(0,1-Math.abs(ax-.4)/.15)}// kaşlarda öfkeli V
   return y};
  const pt=(th,ph,fl)=>{const r=1+fl;return add(C,[ra*r*Math.sin(ph)*Math.sin(th),rb*Math.cos(ph),rc*r*Math.sin(ph)*Math.cos(th)])};
  {const NT=48,NP=22,v=[],nv=[],ix=[];
   for(let i=0;i<=NT;i++){const th=i/NT*2*PI,yr=rimY(th)-.026,pm=Math.acos(Math.max(-.95,Math.min(.95,yr/rb)));
    for(let j=0;j<=NP;j++){const ph=pm*j/NP,fl=Math.max(0,ph-1.6)*.55*(Math.cos(th)<0?1:.3),dent=Math.sin(th*7+ph*5)*.0015,q=pt(th,ph,fl+dent);v.push(...q);
     const nn=nrm([Math.sin(ph)*Math.sin(th)/ra,Math.cos(ph)/rb,Math.sin(ph)*Math.cos(th)/rc]);nv.push(...nn)}}
   for(let i=0;i<NT;i++)for(let j=0;j<NP;j++){const a=i*(NP+1)+j,b=a+NP+1;ix.push(a,a+1,b,b,a+1,b+1)}
   it(mk(v,nv,ix),basis([1,0,0],[0,1,0],[0,0,1],[0,0,0]),IRON,{met:1});
   // kalın kenar, perçinler
   let prev=null;for(let i=0;i<=NT;i++){const th=i/NT*2*PI,yr=rimY(th)-.026,pm=Math.acos(Math.max(-.95,Math.min(.95,yr/rb))),fl=Math.max(0,pm-1.6)*.55*(Math.cos(th)<0?1:.3),q=pt(th,pm,fl+.02);if(prev)seg(prev,q,.0065,.0065,IRD,{met:1,nocap:1});prev=q;
    if(i%3==0&&i<NT)sp(pt(th,pm-.14,fl+.03),[.0055,.0055,.0055],RIV,{met:1})}
   // orta bant + perçin sırası
   prev=null;for(let i=0;i<=24;i++){const ph=-1.45+i/24*2.9,q=add(C,[0,rb*1.04*Math.cos(ph),rc*1.04*Math.sin(ph)]);if(ph<-1.2||ph>1.45){prev=null;continue}if(prev)seg(prev,q,.009,.009,IRD,{met:1,nocap:1,rz:.5});prev=q;if(i%2==0)sp(add(q,mulS(nrm(sub(q,C)),.006)),[.005,.005,.005],RIV,{met:1})}
   // tepe dikenleri (önden arkaya, büyüyüp küçülen)
   for(let i=0;i<7;i++){const ph=-.75+i*.25,b0=add(C,[0,rb*1.07*Math.cos(ph),rc*1.07*Math.sin(ph)]),dir=nrm(sub(b0,C)),h=.03+.03*Math.sin((i+.5)/7*PI);cone(b0,add(b0,add(mulS(dir,h),[0,0,-.012])),.011,IRD,{met:1})}
   // burun koruması
   const nt=pt(0,Math.acos((rimY(0)-.026)/rb),.03);box(add(nt,[0,-.026,.014]),[.0085,.032,.005],IRON,{met:1,R:[[1,0,0],nrm([0,1,-.18]),nrm([0,.18,1])]});cone(add(nt,[0,-.058,.02]),add(nt,[0,-.074,.026]),.0085,IRON,{met:1});
   // yanlarda geriye kıvrık demir boynuzlar
   for(const s of[-1,1]){let pp=pt(s*1.25,1.05,.02),r0=.028;for(let k=0;k<9;k++){const u=(k+1)/9,np=add(pt(s*1.25,1.05,.02),[s*(.02+.11*u),.045*u+.07*u*u,-.02*u+.05*u*u*u]);if(k<8)seg(pp,np,r0,r0*.8,k%3==0?IRD:IRON,{met:1,nocap:1});else cone(pp,add(np,[s*.012,.02,.01]),r0,IRON,{met:1});pp=np;r0*=.82}
    sp(pt(s*1.25,1.05,.025),[.026,.026,.02],IRD,{met:1})}
  }
   // kapalı yüz: çene ve yanakları saran alt plaka, gözlerde dar yarık
   {const NA=36,NB_=16,v=[],ix=[],TH=2.05,Cj=add(HC2,[0,-.035,.004]);
    const yT=th=>{const ax=Math.abs(th);return -.014+.011*Math.min(1,ax/.6)},yB=th=>{const ax=Math.abs(th);return -.108+.03*Math.min(1,ax/1.6)};
    const P_=(th,tb)=>{const y=lerp2(yT(th),yB(th),tb),sq=1-.2*tb*tb,rx=.112*sq,rz=.122*sq*(1-.06*Math.pow(Math.abs(th)/TH,2));return add([0,0,0],add([0,y,0],add([Cj[0]+rx*Math.sin(th),HC2[1],Cj[2]+rz*Math.cos(th)],[0,0,0])))};
    function lerp2(a,b,u){return a+(b-a)*u}
    for(let i=0;i<=NA;i++){const th=-TH+2*TH*i/NA;for(let j=0;j<=NB_;j++)v.push(...P_(th,j/NB_))}
    const g=(i,j)=>{i=Math.max(0,Math.min(NA,i));j=Math.max(0,Math.min(NB_,j));const k=(i*(NB_+1)+j)*3;return[v[k],v[k+1],v[k+2]]},nv=[];
    for(let i=0;i<=NA;i++)for(let j=0;j<=NB_;j++){let n=nrm(cross(sub(g(i+1,j),g(i-1,j)),sub(g(i,j+1),g(i,j-1))));const c=g(i,j);if(n[0]*(c[0]-Cj[0])+n[2]*(c[2]-Cj[2])<0)n=mulS(n,-1);nv.push(...n)}
    for(let i=0;i<NA;i++)for(let j=0;j<NB_;j++){const a=i*(NB_+1)+j,b=a+NB_+1;ix.push(a,a+1,b,b,a+1,b+1)}
    it(mk(v,nv,ix),basis([1,0,0],[0,1,0],[0,0,1],[0,0,0]),IRON,{met:1});
    const out=(th,tb,o)=>{const q=P_(th,tb),d=nrm([q[0]-Cj[0],0,q[2]-Cj[2]]);return add(q,mulS(d,o))};
    // üst ve alt kenar bandı
    for(const tb of[0,1]){let pr=null;for(let i=0;i<=NA;i++){const th=-TH+2*TH*i/NA,q=out(th,tb,.004);if(pr)seg(pr,q,.0055,.0055,IRD,{met:1,nocap:1});pr=q;if(i%4==2)sp(out(th,tb?.88:.14,.005),[.0048,.0048,.0048],RIV,{met:1})}}
    // nefes yarıkları
    for(let k=-3;k<=3;k++){const th=k*.12,q=out(th,.55,.003),d=nrm([q[0]-Cj[0],0,q[2]-Cj[2]]),up=[0,1,0],x=nrm(cross(up,d));box(q,[.0032,.024,.004],'#050506',{R:[x,up,d]})}
    // çenede aşağı bakan dişler
    for(let k=-2;k<=2;k++){const th=k*.17,q=out(th,1,.004);cone(q,add(q,[0,-.03+Math.abs(k)*.007,.012]),.008,IRD,{met:1})}
    // yanak çıkıntıları (dikenli)
    for(const sg of[-1,1]){const q=out(sg*1.05,.45,.004);cone(q,add(q,[sg*.03,-.006,.012]),.009,IRD,{met:1})}
   }
  for(let k=h0;k<L.length;k++)L[k].v1=1});
 /* ---- siyah demir dikenli çizmeler (kalkanla aynı) ---- */
 for(const s of[-1,1]){const A=AN(s),BLK='#17181b',BLD='#0b0b0d',RV='#4c4e53';
  rg(bi(s,14),()=>{const b0=L.length;
   sp(add(A,[-s*.003,-.026,.033]),[.045,.03,.09],BLK,{met:1});
   sp(add(A,[-s*.008,-.024,.092]),[.047,.028,.04],BLK,{met:1});
   box(add(A,[-s*.003,-.054,.034]),[.046,.006,.088],BLD,{met:1});
   for(let i=0;i<3;i++){const z=.0+i*.042;seg(add(A,[-s*.003-.047,-.024,z]),add(A,[-s*.003+.047,-.024,z]),.006,.006,BLD,{met:1,nocap:1,rz:.6});sp(add(A,[-s*.003,.003+(i==2?-.007:0),z]),[.005,.005,.005],RV,{met:1})}
   cone(add(A,[-s*.004,-.02,.122]),add(A,[-s*.004,-.008,.16]),.012,BLD,{met:1});
   cone(add(A,[-s*.003,.004,.078]),add(A,[-s*.003,.034,.094]),.0075,BLD,{met:1});
   for(let k=b0;k<L.length;k++)L[k].v1=1});
  rg(bi(s,12),()=>{const b0=L.length;
   seg(add(A,[0,-.01,-.006]),add(A,[0,.082,-.01]),.044,.049,BLK,{met:1,nocap:1});
   seg(add(A,[0,.076,-.01]),add(A,[0,.09,-.01]),.053,.053,BLD,{met:1,nocap:1});
   seg(add(A,[0,.03,-.008]),add(A,[0,.04,-.008]),.05,.05,BLD,{met:1,nocap:1});
   for(let k=0;k<6;k++){const a=k/6*2*PI+.4,d=[Math.sin(a),0,Math.cos(a)],p0=add(A,add([0,.06,-.009],mulS(d,.047)));cone(p0,add(p0,add(mulS(d,.032),[0,.012,0])),.009,BLD,{met:1})}
   for(let k=0;k<8;k++){const a=k/8*2*PI;sp(add(A,add([0,.083,-.01],[Math.sin(a)*.053,0,Math.cos(a)*.053])),[.0045,.0045,.0045],RV,{met:1})}
   for(let k=b0;k<L.length;k++)L[k].v1=1});
 }
 /* ---- sol ön kola bağlı siyah demir kalkan (yalnız yeni sürüm) ---- */
 rg(6,()=>{const s0=L.length,BLK='#17181b',BLD='#0b0b0d',RV='#4c4e53',BONE='#d9cfb4',El=EL(-1),Wr=WR(-1),mid=lerp(El,Wr,.55),fa=nrm(sub(El,Wr));
  const ez=nrm([-1,0,.38]),ex=nrm(cross(fa,ez)),ey=nrm(cross(ez,ex)),Cs=add(mid,mulS(ez,.045)),Pp=(x,y,z)=>add(Cs,add(mulS(ex,x),add(mulS(ey,y),mulS(ez,z)))),R0=.135;
  const rr=a=>R0*(1+.06*Math.max(0,Math.cos(a*12))**6-.035*Math.max(0,Math.sin(a*12+.6))**8)*(1-.09*Math.max(0,Math.cos(a*3+1.1))**30);
  {const NA=72,NR=10,v=[],nv=[],ix=[];
   for(const side of[1,-1])for(let i=0;i<=NA;i++){const a=i/NA*2*PI;for(let j=0;j<=NR;j++){const t=j/NR,r=rr(a)*t,z=side>0?.022*(1-t*t)+.004:-.002,q=Pp(r*Math.cos(a),r*Math.sin(a),z);v.push(...q);
     const nl=side>0?nrm(add(mulS(ez,1),add(mulS(ex,.022*2*t*Math.cos(a)/R0*2),mulS(ey,.022*2*t*Math.sin(a)/R0*2)))):mulS(ez,-1);nv.push(...nl)}}
   const off=(NA+1)*(NR+1);for(const o of[0,off])for(let i=0;i<NA;i++)for(let j=0;j<NR;j++){const a=o+i*(NR+1)+j,b=a+NR+1;ix.push(a,a+1,b,b,a+1,b+1)}
   // kenar yüzü
   for(let i=0;i<NA;i++){const a=i*(NR+1)+NR,b=(i+1)*(NR+1)+NR;ix.push(a,b,off+a,b,off+b,off+a)}
   it(mk(v,nv,ix),basis([1,0,0],[0,1,0],[0,0,1],[0,0,0]),BLK,{met:1});
   // dişli kenar bandı ve perçinler
   let pr=null;for(let i=0;i<=NA;i++){const a=i/NA*2*PI,q=Pp(rr(a)*.97*Math.cos(a),rr(a)*.97*Math.sin(a),.006);if(pr)seg(pr,q,.006,.006,BLD,{met:1,nocap:1});pr=q;if(i%6==3)sp(Pp(rr(a)*.86*Math.cos(a),rr(a)*.86*Math.sin(a),.009),[.0055,.0055,.004],RV,{met:1})}
   // kenardan dışa sivri dikenler
   for(let k=0;k<8;k++){const a=k/8*2*PI+.2,b0=Pp(rr(a)*.93*Math.cos(a),rr(a)*.93*Math.sin(a),.006),tp=Pp((R0+.05)*Math.cos(a),(R0+.05)*Math.sin(a),.018);cone(b0,tp,.011,BLD,{met:1})}
   // iç halka
   pr=null;for(let i=0;i<=40;i++){const a=i/40*2*PI,q=Pp(.075*Math.cos(a),.075*Math.sin(a),.02);if(pr)seg(pr,q,.004,.004,BLD,{met:1,nocap:1});pr=q}
   // ortada kafatası kabartması, kızıl parlayan gözler
   sp(Pp(0,.012,.026),[.05,.046,.024],BONE,{R:[ex,ey,ez]});sp(Pp(0,-.03,.024),[.032,.022,.018],BONE,{R:[ex,ey,ez]});
   for(const sg of[-1,1]){sp(Pp(sg*.019,.008,.044),[.014,.012,.008],'#0a0505',{R:[ex,ey,ez]});sp(Pp(sg*.019,.008,.049),[.006,.006,.004],'#ff2a10',{em:1,R:[ex,ey,ez]})}
   cone(Pp(0,-.008,.046),Pp(0,-.018,.05),.006,'#120908');
   for(let k=-3;k<=3;k++)cone(Pp(k*.008,-.034,.04),Pp(k*.0085,-.05-Math.abs(k%2)*.004,.04),.0042,'#efe6c8');
   // kafatasının tepesinde boynuz gibi kıvrılan iki diken
   for(const sg of[-1,1]){let pp=Pp(sg*.035,.045,.03),r0=.012;for(let k=0;k<5;k++){const u=(k+1)/5,np=Pp(sg*(.035+.05*u),.045+.035*u+.02*u*u,.03+.02*u);if(k<4)seg(pp,np,r0,r0*.78,BLD,{met:1,nocap:1});else cone(pp,np,r0,BLD,{met:1});pp=np;r0*=.78}}
   // tutma kayışı (kalkanın arkası)
   seg(Pp(-.04,.0,-.004),add(lerp(El,Wr,.4),mulS(ez,.012)),.008,.008,'#2a1a0e',{nocap:1});seg(Pp(.04,-.02,-.004),add(lerp(El,Wr,.8),mulS(ez,.012)),.008,.008,'#2a1a0e',{nocap:1});
  }
  for(let k=s0;k<L.length;k++){L[k].v1=1;L[k].shd=1}});
 // kemer, peştamal
 rg(0,()=>{seg([0,.438,0],[0,.47,0],.142,.142,'#3a2412',{nocap:1,rz:.8});box([0,.455,.112],[.04,.032,.01],GOLD,{met:1});sp([0,.455,.118],[.012,.012,.006],'#8a1a14',{em:.2});
  box([0,.37,.108],[.13,.17,.008],'#4a1814');L[L.length-1].v0=1;box([0,.29,.11],[.13,.012,.009],GOLD,{met:1});L[L.length-1].v0=1;box([0,.375,-.104],[.15,.16,.008],'#33100c');L[L.length-1].v0=1;for(const s of[-1,1]){box([s*.128,.4,0],[.008,.1,.1],'#4a1814');L[L.length-1].v0=1}});
 // gövde: kayış, göğüs plakası, kolye, pelerin
 rg(1,()=>{seg([.17,.72,.02],[-.13,.47,.1],.013,.013,'#3a2412',{rz:.45});seg([.17,.72,-.03],[-.13,.47,-.09],.013,.013,'#3a2412',{rz:.45});
  disc([-.072,.66,.115],nrm([-.15,.25,1]),.048,.008,GOLD,{met:1});sp([-.072,.66,.122],[.02,.022,.012],'#e9e2cc');for(const e of[-1,1])sp([-.072+e*.007,.663,.132],[.004,.005,.003],'#140c08');
  for(let i=0;i<11;i++){const a=PI*(.12+.76*i/10),p=[Math.cos(a)*.085,.725-Math.sin(a)*.045,.07+Math.sin(a)*.03];cone(p,add(p,[0,-.028,.006]),.0065,'#efe6c8')}
  seg([-.17,.722,-.07],[.17,.722,-.07],.018,.018,'#5a1410',{rz:.7});for(const e of[-1,1])disc([e*.15,.73,-.04],nrm([e,.3,.2]),.022,.006,'#c99a3a',{met:1})});
 // omuzluklar (kemik)
 for(const s of[-1,1])rg(bi(s,4),()=>{const P0=add(SH(s),[s*.012,.03,0]);sp(P0,[.075,.05,.072],'#e9e2cc');sp(add(P0,[0,-.024,0]),[.08,.01,.076],'#cfc4a4');for(let i=-1;i<=1;i++){const b0=add(P0,[s*.02+i*.018,.035,i*.03]);cone(b0,add(b0,[s*.025,.06-Math.abs(i)*.018,i*.008]),.012,'#efe6c8')}});
 for(const s of[-1,1])rg(bi(s,8),()=>{for(const[p,d]of TIPS[s])sp(add(p,mulS(d,.002)),[.006,.0035,.006],'#2a2418',{R:[nrm(cross(d,[0,0,1])),d,nrm(cross(nrm(cross(d,[0,0,1])),d))]})});
 for(const s of[-1,1])rg(bi(s,14),()=>{for(const[p,r]of TOES[s])sp(add(p,[0,r*.4,.001]),[r*.8,r*.35,r*.7],'#2a2418')});
 for(const s of[-1,1])rg(bi(s,12),()=>{const A=AN(s);seg(add(A,[0,.03,0]),add(A,[0,.05,0]),.031,.033,'#3a2412',{nocap:1});seg(add(A,[0,.052,0]),add(A,[0,.058,0]),.034,.034,'#c99a3a',{nocap:1,met:1})});
 // bileklikler
 for(const s of[-1,1])rg(bi(s,6),()=>{const El=EL(s),W=WR(s);seg(lerp(El,W,.5),lerp(El,W,.92),.041,.034,'#8a6a2a',{nocap:1,met:1});seg(lerp(El,W,.55),lerp(El,W,.6),.043,.042,'#3a2412',{nocap:1})});
 // satır (sağ el)
 rg(9,()=>{const c0=L.length;const Wc=add(WR(1),[0,-.04,.004]),z=[0,.12,1],u=nrm(z),x=[1,0,0],w=nrm(cross(u,x));
  const K=1.1;seg(sub(Wc,mulS(u,.09*K)),add(Wc,mulS(u,.2*K)),.017*K,.015*K,'#3a2412');for(let i=0;i<4;i++)seg(add(Wc,mulS(u,(-.06+i*.02)*K)),add(Wc,mulS(u,(-.052+i*.02)*K)),.019*K,.019*K,'#1e140c',{nocap:1});
  sp(sub(Wc,mulS(u,.095*K)),[.022*K,.018*K,.022*K],GOLD,{met:1});
  const o=add(Wc,mulS(u,.19*K));it(BLADE.body,basis(mulS(x,K),mulS(u,K),mulS(w,K),o),'#7c838c',{met:1});it(BLADE.edge,basis(mulS(x,K),mulS(u,K),mulS(w,K),o),'#e6ebef',{met:1});
  sp(add(o,add(mulS(x,.035*K),mulS(u,.05*K))),[.016*K,.016*K,.016*K],GOLD,{met:1});sp(add(o,add(mulS(x,.035*K),mulS(u,.05*K))),[.007*K,.007*K,.022*K],'#8a1a14',{em:.3});for(let k=c0;k<L.length;k++)L[k].cl=1});
})();
/* --- kemik animasyonu --- */
const Tm=v=>new Float32Array([1,0,0,0,0,1,0,0,0,0,1,0,v[0],v[1],v[2],1]),rX=a=>{const c=Math.cos(a),s=Math.sin(a);return new Float32Array([1,0,0,0,0,c,s,0,0,-s,c,0,0,0,0,1])},rZ=a=>{const c=Math.cos(a),s=Math.sin(a);return new Float32Array([c,s,0,0,-s,c,0,0,0,0,1,0,0,0,0,1])},rYm=a=>rotY(a);
function pose(ph,walking,t,seed,dt_){const R=[];for(let b=0;b<NB;b++)R[b]=new Float32Array([1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1]);let bob=0;
 const sm=x=>{x=Math.min(1,Math.max(0,x));return x*x*(3-2*x)},hs=n=>{const v=Math.sin(n*127.1+seed*311.7)*43758.5453;return v-Math.floor(v)},lerp=(a,b,u)=>a+(b-a)*u;
 const dead=dt_!==undefined&&dt_!==null;const wk=walking?1:0;
 if(!dead){
  /* bacaklar */
  for(const s of[-1,1]){const p=ph+(s>0?0:PI),a=Math.sin(p)*.42*wk,kb=(.12+.62*Math.max(0,Math.cos(p)))*wk+.06*(1-wk);R[bi(s,10)]=rX(-a);R[bi(s,12)]=rX(kb);R[bi(s,14)]=rX(a*.85-kb*.85)}
  bob=(-Math.abs(Math.sin(ph))*.012+.006)*wk;
  /* gövde */
  R[0]=mmul(rYm(Math.sin(ph)*.07*wk),rZ(Math.sin(ph)*.03*wk));
  /* satır sallama: rastgele aralıklarla tepeden vuruş ya da yandan savurma */
  const per=2.4,k=Math.floor((t+seed*9)/per),st=k*per-seed*9,on=hs(k)<.62,off=.15+hs(k+.5)*(per-1.1),u=on?(t-st-off)/.95:-1,typ=hs(k+.25)<.55?0:1;
  const fwdR=-Math.sin(ph)*wk;// sağ kol bacağa karşı salınır
  let sh=-.32-fwdR*.1,sz=.1,el=-1.227+Math.sin(ph-.4)*.173,wr=.05+Math.sin(ph-.8)*.06,ch=0;
  if(u>0&&u<1){const K=typ==0?[[-2.45,.28,-1.95,-.45,-.22],[-.5,.04,-.2,.4,.32]]:[[-1.25,.95,-.95,.05,-.5],[-1.15,-.55,-.3,.25,.55]];
   const w=sm(u/.38),x=sm((u-.42)/.16),r=sm((u-.68)/.32);const base=[sh,sz,el,wr,ch];const v=base.map((b,i)=>{let a=lerp(b,K[0][i],w);a=lerp(a,K[1][i],x);return lerp(a,b,r)});[sh,sz,el,wr,ch]=v}
  R[1]=mmul(rYm(-Math.sin(ph)*.1+ch),rX(.06+Math.abs(ch)*.12));R[3]=rX(Math.sin(ph*2)*.04-ch*.15);
  R[5]=mmul(rX(sh),rZ(sz));R[7]=rX(el);R[9]=mmul(rX(wr),rZ(-.05));
  /* sol kol: omuz-dirsek-bilek aynı ritimde, dirsek gecikmeli kırılır */
  const fwdL=Math.sin(ph)*wk,lag=Math.sin(ph-.45)*wk,lag2=Math.sin(ph-.9)*wk;
  R[4]=mmul(rX(-fwdL*.46-ch*.4),rZ(-.13-Math.abs(fwdL)*.03));
  R[6]=rX(-.536-Math.max(0,lag)*.622-Math.max(0,-lag)*.104);
  R[8]=mmul(rX(-.08-lag2*.18),rZ(lag2*.06));
 }else{
  /* ölüm: sarsılır, kalkanı düşer, tek dizinin üstüne çöker, satırı düşer, sonra yüzüstü kapaklanır */
  const d=dt_,b=sm(d/.16)*(1-sm((d-.16)/.22)),k=sm((d-.5)/.4),lp=sm((d-2.0)/.35),side=hs(3)<.5?-1:1,shk=d<.6?Math.sin(d*40)*Math.exp(-d*5)*.06:0;
  const kn=-1;
  R[bi(kn,10)]=rX(-.35*b-.1*k-.3*lp);R[bi(kn,12)]=rX(.3*b+1.6*k-.3*lp);R[bi(kn,14)]=rX(-.2*b-.6*k+.35*lp);
  R[bi(-kn,10)]=rX(-.25*b-1.3*k+.6*lp);R[bi(-kn,12)]=rX(.2*b+1.45*k-.6*lp);R[bi(-kn,14)]=rX(-.15*k+.2*lp);
  R[0]=mmul(rZ(.06*k),rX(-.06*b));
  const sl=sm((d-.22)/.25),rel=sm((d-1.25)/.2),sag=sm((d-1.0)/.6);
  R[1]=rX(-.4*b+.28*k+.1*sag+shk+.05*lp);R[2]=rX(-.2*b+.1*k);R[3]=mmul(rX(-.55*b+.35*k+.2*sag+shk*1.5-.3*lp),rZ(side*.3*lp));
  R[4]=mmul(rX(-.7*b+.25*sl-1.1*lp),rZ(-.55*b-.05*sl-.55*lp));R[6]=rX(-.4*b*(1-sl)-.1-.3*lp);R[8]=rX(.25*sl);
  R[5]=mmul(rX(-1.0*b-.35*k*(1-rel)+.1*rel-1.0*lp),rZ(.5*b+.12*k+.55*lp));R[7]=rX(-1.2*(1-k*.45)*(1-rel*.6)-.1);R[9]=rX(.3*rel);
 }
 const W=[],S=[];for(let b=0;b<NB;b++){const p=PAR[b];if(p<0)W[b]=mmul(Tm(add(J[b],[0,bob,0])),R[b]);else W[b]=mmul(W[p],mmul(Tm(sub(J[b],J[p])),R[b]));S[b]=mmul(W[b],Tm(mulS(J[b],-1)))}
 // ayakları zemine oturt
 let minY=1e9;for(const s of[-1,1]){const w=S[bi(s,14)],a=AN(s),f=[a[0],a[1]-.05,a[2]+.04],y=w[1]*f[0]+w[5]*f[1]+w[9]*f[2]+w[13];minY=Math.min(minY,y)}
 if(dt_!==undefined&&dt_!==null)for(const s of[-1,1]){const w=S[bi(s,12)],a=add(KN(s),[0,-.035,.025]),y=w[1]*a[0]+w[5]*a[1]+w[9]*a[2]+w[13];minY=Math.min(minY,y)}
 const dy=.004-minY;for(let b=0;b<NB;b++)S[b]=mmul(Tm([0,dy,0]),S[b]);return S}
/* --- GPU: deri tamponları (VAO) --- */
const SKV=gl.createVertexArray();gl.bindVertexArray(SKV);
for(const[loc,data,sz]of[[0,MESH.P,3],[1,MESH.N,3],[2,MESH.Cl,3],[3,MESH.AM,2],[4,MESH.BI,4],[5,MESH.BW,4]]){const b=gl.createBuffer();gl.bindBuffer(gl.ARRAY_BUFFER,b);gl.bufferData(gl.ARRAY_BUFFER,data,gl.STATIC_DRAW);gl.enableVertexAttribArray(loc);gl.vertexAttribPointer(loc,sz,gl.FLOAT,false,0,0);gl.vertexAttribDivisor(loc,0)}
const SKI=gl.createBuffer();gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER,SKI);gl.bufferData(gl.ELEMENT_ARRAY_BUFFER,MESH.IX,gl.STATIC_DRAW);gl.bindVertexArray(null);
/* --- gölgelendiriciler: oyunun ışık ve sisiyle uyumlu --- */
const FSC=`#version 300 es
precision highp float;precision highp sampler2DShadow;in vec3 vn,vw,vc,vr;in vec2 vam;in vec4 vl;uniform vec3 uCam,uL,uFogC;uniform float uFogS,em,met,kind,fl;uniform sampler2DShadow uSh;out vec4 o;
float hs(vec3 p){return fract(sin(dot(p,vec3(127.1,311.7,74.7)))*43758.5453);}
float vn3(vec3 p){vec3 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(mix(hs(i),hs(i+vec3(1,0,0)),f.x),mix(hs(i+vec3(0,1,0)),hs(i+vec3(1,1,0)),f.x),f.y),mix(mix(hs(i+vec3(0,0,1)),hs(i+vec3(1,0,1)),f.x),mix(hs(i+vec3(0,1,1)),hs(i+vec3(1,1,1)),f.x),f.y),f.z);}
float fbm(vec3 p){return vn3(p)*.55+vn3(p*2.1)*.28+vn3(p*4.3)*.17;}
float shadowAt(vec3 n){vec3 p=vl.xyz/vl.w*.5+.5;if(p.x<0.||p.x>1.||p.y<0.||p.y>1.||p.z>1.)return 1.;float b=.0016+.004*(1.-max(dot(n,uL),0.));float s=0.;float tx=1./${SHN}.;for(int i=0;i<2;i++)for(int j=0;j<2;j++)s+=texture(uSh,vec3(p.xy+(vec2(float(i),float(j))-.5)*tx*1.7,p.z-b));return s/4.;}
vec3 aces(vec3 x){return clamp((x*(2.51*x+.03))/(x*(2.43*x+.59)+.14),0.,1.);}
void main(){vec3 N=normalize(vn);vec3 V=normalize(uCam-vW());if(vam.y>.5){if(!gl_FrontFacing)N=-N;}else if(dot(N,V)<0.)N=-N;vec3 base=vc;float ao=vam.x,skin=vam.y;
 if(skin>.5){float e=.004;vec3 q=vr*70.;float b0=fbm(q);vec3 gr=vec3(fbm(q+vec3(e*70.,0,0))-b0,fbm(q+vec3(0,e*70.,0))-b0,fbm(q+vec3(0,0,e*70.))-b0);N=normalize(N-gr*.18);base*=.93+.12*fbm(vr*10.);base=mix(base*vec3(.75,.7,.6),base,smoothstep(.35,.9,ao));}
 else if(met<.5){base*=.82+.3*fbm(vr*60.);}
 if(met>.5)base*=.85+.25*vn3(vW()*120.);
 float sh=shadowAt(N);float nd=dot(N,uL),d=max(nd,0.),wrap=skin>.5?max((nd+.35)/1.35,0.):d;
 vec3 amb=mix(vec3(.30,.26,.20),vec3(.40,.52,.72),.5+.5*N.y)*ao;
 vec3 lit=base*(amb*1.15+vec3(1.35,1.12,.86)*wrap*mix(.3,1.,sh));
 if(skin>.5)lit+=base*vec3(.55,.18,.08)*clamp(wrap-d,0.,1.)*.9*sh;
 vec3 H=normalize(uL+V);float spw=met>.5?70.:(skin>.5?22.:10.),spi=met>.5?1.1:(skin>.5?.2:.05);lit+=vec3(1.,.95,.85)*pow(max(dot(N,H),0.),spw)*spi*d*sh;
 float rim=pow(1.-max(dot(N,V),0.),3.);lit+=rim*vec3(.35,.45,.65)*.18*(base+.1)*ao;
 lit=mix(lit,base*1.7+.12,min(em,1.));lit=mix(lit,vec3(1.,.97,.92),fl*.75);
 float dist=length(uCam-vW());float f=1.-exp(-pow(max(dist-uFogS,0.)*(.42/uFogS),1.4));lit=mix(lit,uFogC,f);
 lit=aces(lit*.86);float lum=dot(lit,vec3(.3,.59,.11));lit=mix(vec3(lum),lit,1.03);o=vec4(lit,1.);}`.replace(/vW\(\)/g,'vw');
const VSK=`#version 300 es
layout(location=0) in vec3 p;layout(location=1) in vec3 n;layout(location=2) in vec3 c;layout(location=3) in vec2 am;layout(location=4) in vec4 bi;layout(location=5) in vec4 bw;
uniform mat4 B[${NB}];uniform mat4 VP,R,LVP;out vec3 vn,vw,vc,vr;out vec2 vam;out vec4 vl;
void main(){mat4 S=B[int(bi.x)]*bw.x+B[int(bi.y)]*bw.y+B[int(bi.z)]*bw.z+B[int(bi.w)]*bw.w;vec4 w=R*S*vec4(p,1.);vw=w.xyz;vn=mat3(R*S)*n;vc=c;vr=p;vam=am;vl=LVP*w;gl_Position=VP*w;}`;
const VPR=`#version 300 es
layout(location=0) in vec3 p;layout(location=1) in vec3 n;uniform mat4 M,VP,LVP;uniform mat3 NM;uniform vec3 col;out vec3 vn,vw,vc,vr;out vec2 vam;out vec4 vl;
void main(){vec4 w=M*vec4(p,1.);vw=w.xyz;vn=NM*n;vc=col;vr=p*.3+w.xyz;vam=vec2(1.,0.);vl=LVP*w;gl_Position=VP*w;}`;
const DFS=`#version 300 es
precision mediump float;out vec4 o;void main(){o=vec4(1.);}`;
function shc(t,s){const o=gl.createShader(t);gl.shaderSource(o,s);gl.compileShader(o);if(!gl.getShaderParameter(o,gl.COMPILE_STATUS))throw new Error(gl.getShaderInfoLog(o));return o}
function prog(v,f,names){const p=gl.createProgram();gl.attachShader(p,shc(gl.VERTEX_SHADER,v));gl.attachShader(p,shc(gl.FRAGMENT_SHADER,f));gl.linkProgram(p);if(!gl.getProgramParameter(p,gl.LINK_STATUS))throw new Error(gl.getProgramInfoLog(p));const u={};for(const n of names)u[n]=gl.getUniformLocation(p,n);return{p,u}}
const UN=['VP','R','LVP','M','NM','col','B','uCam','uL','uFogC','uFogS','em','met','kind','fl','uSh'];
const PS=prog(VSK,FSC,UN),PP=prog(VPR,FSC,UN),DS=prog(VSK,DFS,UN),DP=prog(VPR,DFS,UN);
/* --- kuyruk ve çizim --- */
const QU=[];
function queue(e,dead,ct){
 const tg=Math.atan2(e.ux===undefined?1:e.ux,e.uy||0);if(e.hc===undefined)e.hc=tg;else{let d=tg-e.hc;while(d>PI)d-=PI*2;while(d<-PI)d+=PI*2;e.hc+=d*.2}
 const H=heightOf(e),X=e.c-N/2,Z=e.r;
 if(e.cs===undefined)e.cs=Math.random();const q={sd:e.cs,X,Z,H,a:e.hc,ph:e.ph||0,dead,ct,fl:!dead&&e.fl>0?1:0,slow:!dead&&e.slow>0,w:(e.wob||0)*3};
 q.S=pose(dead?0:q.ph,!dead,time+q.sd*50,q.sd,dead?ct:null);q.R=rootM(q);
 if(!dead){prim(GD_,mT(X,.018,Z),[.24*H,1,.2*H],[0,0,0],0,.42);
  for(const s of[-1,1]){const fp=xf(mmul(q.R,q.S[bi(s,14)]),add(AN(s),[0,-.05,.04])),hh=Math.max(0,fp[1]),al=.62*Math.max(0,1-hh/(.07*H)),r=.075*H*(1+hh/(.1*H));if(al>.02)prim(GD_,mT(fp[0],.022,fp[2]),[r,1,r],[0,0,0],0,al)}}
 QU.push(q);return H}
function rootM(q){const S=q.H,sc=new Float32Array([S,0,0,0,0,S,0,0,0,0,S,0,0,0,0,1]);let M=mmul(Tm([q.X,0,q.Z]),rotY(q.a));
 if(q.dead){const ct=q.ct,hv=Math.sin(q.sd*311.7)*43758.5453,side=(hv-Math.floor(hv))<.5?-1:1;
  const f=Math.min(1,Math.max(0,(ct-1.6)/.42)),fe=f*f*f*.4+f*f*.6,tb=ct-2.02,bn=tb>0?Math.sin(tb*16)*Math.exp(-tb*7)*.08:0,kick=ct<.3?Math.sin(ct/.3*PI)*.035:0,sway=ct>.9&&ct<1.6?Math.sin((ct-.9)*6)*.025*(1-(ct-.9)/.7):0,sink=Math.max(0,ct-3.2)/.85;
  const pv=[0,.03,.06],ang=fe*1.3-bn+sway;
  M=mmul(Tm([q.X,-sink*.6*q.H,q.Z]),mmul(rotY(q.a+side*fe*.18),mmul(Tm([0,0,-kick*q.H]),mmul(Tm(mulS(pv,q.H)),mmul(rZ(side*fe*.12),mmul(rX(ang),Tm(mulS(pv,-q.H))))))))}
 return mmul(M,sc)}
/* sert parçaları tek tamponlarda birleştir (çizim sayısını azaltır) */
const GRP=(()=>{const M={};for(const d of RG){if(d.v0)continue;const key=[d.b,d.c.map(x=>x.toFixed(3)).join(','),d.e,d.m,d.cl?1:0,d.shd?1:0].join('|');(M[key]||(M[key]={b:d.b,c:d.c,e:d.e,m:d.m,cl:!!d.cl,shd:!!d.shd,it:[]})).it.push(d)}
 const out=[];for(const k in M){const G_=M[k],P=[],Nn=[],I=[];for(const d of G_.it){const g=d.g;if(!g.cv)continue;const base=P.length/3,m=d.M,nm=nmat(m);
   for(let q=0;q<g.cv.length;q+=3){const x=g.cv[q],y=g.cv[q+1],z=g.cv[q+2];P.push(m[0]*x+m[4]*y+m[8]*z+m[12],m[1]*x+m[5]*y+m[9]*z+m[13],m[2]*x+m[6]*y+m[10]*z+m[14]);
    const a=g.cn[q],b=g.cn[q+1],c=g.cn[q+2],nx=nm[0]*a+nm[3]*b+nm[6]*c,ny=nm[1]*a+nm[4]*b+nm[7]*c,nz=nm[2]*a+nm[5]*b+nm[8]*c,l=Math.hypot(nx,ny,nz)||1;Nn.push(nx/l,ny/l,nz/l)}
   for(const t of g.ci)I.push(t+base)}
  if(!I.length)continue;const o={b:G_.b,c:G_.c,e:G_.e,m:G_.m,cl:G_.cl,shd:G_.shd,n:I.length,vao:gl.createVertexArray()};gl.bindVertexArray(o.vao);
  for(const[loc,dat]of[[0,P],[1,Nn]]){const bf=gl.createBuffer();gl.bindBuffer(gl.ARRAY_BUFFER,bf);gl.bufferData(gl.ARRAY_BUFFER,new Float32Array(dat),gl.STATIC_DRAW);gl.enableVertexAttribArray(loc);gl.vertexAttribPointer(loc,3,gl.FLOAT,false,0,0)}
  const ib=gl.createBuffer();gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER,ib);gl.bufferData(gl.ELEMENT_ARRAY_BUFFER,new Uint32Array(I),gl.STATIC_DRAW);gl.bindVertexArray(null);out.push(o)}
 return out})();
const I4=new Float32Array([1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1]),DUSTC=[.36,.3,.22];
function xf(M,p){return[M[0]*p[0]+M[4]*p[1]+M[8]*p[2]+M[12],M[1]*p[0]+M[5]*p[1]+M[9]*p[2]+M[13],M[2]*p[0]+M[6]*p[1]+M[10]*p[2]+M[14]]}
function dropM(q,bone,RL,gp,floor,tz,tx){if(!(q.dead&&q.ct>RL))return null;const SC=q.H,Sr=pose(0,false,0,q.sd,RL),Rb=rootM(Object.assign({},q,{ct:RL})),Mr=mmul(Rb,Sr[bone]),gw=xf(Mr,gp);
 const tt=q.ct-RL,h=Math.max(.001,gw[1]-floor*SC),fallT=Math.sqrt(h/4.9),dr=Math.min(h,4.9*tt*tt),tl=Math.min(1,Math.max(0,(tt-fallT)/.3)),tle=tl*tl,bb=tl>=1?Math.sin((tt-fallT-.3)*20)*Math.exp(-(tt-fallT-.3)*8)*.06:0,piv=[gw[0],gw[1]-dr-floor*SC,gw[2]];
 return mmul(Tm(piv),mmul(rZ(tz*(tle-bb*.7)),mmul(rX(tx*tle),mmul(Tm([-piv[0],-piv[1],-piv[2]]),mmul(Tm([0,-dr,0]),Mr)))))}
function pass(depth){if(!QU.length)return;
 const cull=gl.isEnabled(gl.CULL_FACE);if(cull)gl.disable(gl.CULL_FACE);
 for(const q of QU){
  const S=q.S,R=q.R,Bf=new Float32Array(NB*16);for(let b=0;b<NB;b++)Bf.set(S[b],b*16);
  const setU=(pr)=>{gl.useProgram(pr.p);gl.uniformMatrix4fv(pr.u.VP,false,depth?LVP:VP);gl.uniformMatrix4fv(pr.u.LVP,false,LVP);if(!depth){gl.uniform3fv(pr.u.uCam,EYE);gl.uniform3fv(pr.u.uL,SUN);gl.uniform3fv(pr.u.uFogC,FOG);gl.uniform1f(pr.u.uFogS,FOGS);gl.uniform1i(pr.u.uSh,1);gl.uniform1f(pr.u.fl,q.fl)}};
  const ps=depth?DS:PS;setU(ps);gl.uniformMatrix4fv(ps.u.R,false,R);gl.uniformMatrix4fv(ps.u.B,false,Bf);if(!depth){gl.uniform1f(ps.u.em,0);gl.uniform1f(ps.u.met,0);gl.uniform1f(ps.u.kind,1)}
  gl.bindVertexArray(SKV);gl.drawElements(gl.TRIANGLES,MESH.ni,gl.UNSIGNED_INT,0);
  const pp=depth?DP:PP;setU(pp);capeUpdate(time+q.w,!q.dead);
  const CLM=dropM(q,9,1.3,WR(1),.12,-1.45,.25),SHM=dropM(q,6,.42,lerp(EL(-1),WR(-1),.55),.13,1.5,-.2);
  const list=GRP.map(o=>({g:o,M:(CLM&&o.cl)?CLM:(SHM&&o.shd)?SHM:mmul(R,S[o.b]),c:o.c,e:o.e,m:o.m,u32:1}));
  const cf0=q.dead?Math.min(1,Math.max(0,(q.ct-1.55)/.45)):0,cf=cf0*cf0*(3-2*cf0),CS=new Float32Array([1,0,0,0,0,1-.25*cf,0,0,0,0,1-.82*cf,0,0,.03*cf,.02*cf,1]);
  list.push({g:CAPE2,M:mmul(R,mmul(S[1],CS)),c:hx('#6a110c'),e:0,m:0});
  if(q.dead&&q.ct>2&&q.ct<3&&!depth){const u=q.ct-2,cw=xf(mmul(R,S[1]),J[1]),SC=q.H;
   for(let k=0;k<10;k++){const a=k/10*2*PI+.3,rd=(.08+.3*u)*SC*(.7+.5*Math.sin(k*3.7)),sz=SC*(.03+.07*Math.sin(Math.min(1,u*1.6)*PI)*(.6+.4*Math.sin(k*2.1)));if(sz>0)list.push({g:GS,M:basis([sz,0,0],[0,sz*.7,0],[0,0,sz],[cw[0]+Math.cos(a)*rd,SC*(.02+.06*u*(.5+.5*Math.sin(k*1.3))),cw[2]+Math.sin(a)*rd*.8]),c:DUSTC,e:0,m:0})}}
  for(const d of list){gl.uniformMatrix4fv(pp.u.M,false,d.M);gl.uniformMatrix3fv(pp.u.NM,false,nmat(d.M));if(!depth){gl.uniform3fv(pp.u.col,q.slow?[d.c[0]*.75,d.c[1]*.9,Math.min(1,d.c[2]*1.3+.08)]:d.c);gl.uniform1f(pp.u.em,d.e);gl.uniform1f(pp.u.met,d.m);gl.uniform1f(pp.u.kind,0)}gl.bindVertexArray(d.g.vao);gl.drawElements(gl.TRIANGLES,d.g.n,d.u32?gl.UNSIGNED_INT:gl.UNSIGNED_SHORT,0)}
 }
 gl.bindVertexArray(null);if(cull)gl.enable(gl.CULL_FACE);if(!depth)QU.length=0}
return{queue,pass,verts:MESH.nv};

}catch(err){console.error('Ork Şefi modülü yüklenemedi',err);return undefined}})();
