/* Kale Nöbeti · Ork Şefi: tek parça iskeletli deri (oyuna bağlanan modül) */
const GOB=(()=>{try{
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
/* --- iskelet (goblin: kısa bacak, uzun kol, iri baş, kambur) --- */
const J=[[0,.33,0],[0,.46,.015],[0,.56,.05],[0,.63,.085]];const PAR=[-1,0,1,2];
const SH=s=>[s*.118,.53,.02],EL=s=>[s*.165,.415,.045],WR=s=>[s*.185,.3,.08],HP=s=>[s*.058,.32,0],KN=s=>[s*.072,.185,.03],AN=s=>[s*.078,.052,-.01];
J[4]=SH(-1);J[5]=SH(1);J[6]=EL(-1);J[7]=EL(1);J[8]=WR(-1);J[9]=WR(1);J[10]=HP(-1);J[11]=HP(1);J[12]=KN(-1);J[13]=KN(1);J[14]=AN(-1);J[15]=AN(1);
PAR[4]=1;PAR[5]=1;PAR[6]=4;PAR[7]=5;PAR[8]=6;PAR[9]=7;PAR[10]=0;PAR[11]=0;PAR[12]=10;PAR[13]=11;PAR[14]=12;PAR[15]=13;
const NB=16,bi=(s,base)=>base+(s>0?1:0),TIPS={},TOES={};
/* --- vücut primitifleri --- */
const PR=[];
function E(c,r,b,k,ax,sub){const R=ax||[[1,0,0],[0,1,0],[0,0,1]];PR.push({t:'e',c,r,R,b,k,sub})}
function Cc(a,bb,r1,r2,b,k,sub){PR.push({t:'c',a,b2:bb,r1,r2,b,k,sub})}
function Ealong(A,B,t,rx,ry,rz,off,b,k){const d=nrm(sub(B,A)),[x,z]=frame(d,[0,0,1]);E(add(lerp(A,B,t),off),[rx,ry,rz],b,k,[x,d,z])}
// gövde: sıska göğüs, şiş göbek, kambur sırt
E([0,.335,0],[.072,.046,.056],0,.026);
E([0,.392,.008],[.052,.055,.046],0,.022);
E([0,.468,.012],[.096,.064,.064],1,.03);
E([0,.43,.008],[.062,.03,.05],1,.02);
E([0,.505,-.03],[.088,.06,.05],1,.028);
E([0,.535,.0],[.085,.03,.05],1,.02);
E([0,.405,.052],[.006,.006,.006],0,.003,null,1);
for(let k=0;k<5;k++)E([0,.53-k*.035,-.07+k*.006+(k<2?-.004:0)],[.012,.01,.01],1,.008);
for(const s of[-1,1]){
 E([s*.045,.49,.06],[.042,.026,.022],1,.012);
 Cc([s*.018,.535,.05],[s*.105,.54,.03],.0085,.0075,1,.008);
 E([s*.058,.505,-.062],[.035,.04,.016],1,.012);
 for(let r=0;r<3;r++)E([s*.052,.468-r*.022,.05-r*.004],[.024,.005,.012],1,.008);
 const S=SH(s),El=EL(s),W=WR(s),ua=bi(s,4),fa=bi(s,6),hd=bi(s,8);
 E(add(S,[s*.008,.004,0]),[.036,.032,.034],ua,.018);
 Cc(S,El,.025,.02,ua,.014);
 Ealong(S,El,.45,.026,.048,.025,[0,0,.012],ua,.01);
 Cc(El,W,.022,.015,fa,.012);
 E(add(El,[0,.004,-.016]),[.011,.012,.01],fa,.006);
 Ealong(El,W,.3,.027,.045,.024,[s*.004,0,.006],fa,.01);
 // el: uzun kemikli parmaklar
 Cc(add(W,[0,.006,0]),add(W,[0,-.016,.002]),.017,.016,hd,.008);
 E(add(W,[s*.002,-.028,.003]),[.019,.024,.011],hd,.007);
 const grip=s>0;TIPS[s]=[];
 for(let i=0;i<4;i++){const z=-.0125+i*.0083,lenF=[.95,1.05,1,.85][i],rr=[.0056,.006,.0056,.005][i];let p=add(W,[s*.002,-.047,z]);E(p,[.0072,.0066,.007],hd,.0025);
  Cc(add(W,[s*.004,-.02,z*.8]),p,.0032,.0035,hd,.002);
  let d=[0,-1,0];const segL=[.02,.016,.012].map(x=>x*lenF);
  for(let k=0;k<3;k++){d=grip?nrm(add(d,[-s*.75,.18,0])):nrm(add(d,[0,.0,.28]));const n=add(p,mulS(d,segL[k]));Cc(p,n,rr*(1-k*.13),rr*(.84-k*.14),hd,.0016);if(k<2){E(n,[rr*1.22,rr*1.15,rr*1.22],hd,.0012);E(add(n,mulS(d,-.002)),[rr*.9,rr*.45,rr*.9],hd,.001,null,1)}p=n}
  TIPS[s].push([p,d])}
 {let p=add(W,[-s*.002,-.024,.015]);let d=nrm([-s*.1,-.6,.7]);for(let k=0;k<2;k++){if(grip)d=nrm(add(d,[-s*.5,-.1,-.3]));const n=add(p,mulS(d,.015-k*.003));Cc(p,n,.007-k*.001,.006-k*.0012,hd,.003);p=n}TIPS[s].push([p,d])}
 // bacaklar: sıska ama kaslı
 const Hp=HP(s),K=KN(s),A=AN(s),th=bi(s,10),cf=bi(s,12),ft=bi(s,14);
 Cc(Hp,K,.034,.024,th,.016);
 Ealong(Hp,K,.45,.034,.062,.031,[s*.004,0,.02],th,.008);
 Ealong(Hp,K,.4,.03,.06,.027,[0,0,-.016],th,.008);
 E(add(K,[0,.003,.018]),[.019,.02,.013],cf,.007);
 Cc(K,A,.021,.013,cf,.008);
 Ealong(K,A,.3,.026,.048,.024,[0,0,-.016],cf,.007);
 // büyük, uzun ayaklar
 E(add(A,[0,-.024,.032]),[.026,.016,.06],ft,.011);
 E(add(A,[0,-.026,-.014]),[.02,.018,.022],ft,.009);
 for(const e of[-1,1])E(add(A,[e*.019,.003,0]),[.007,.009,.008],cf,.006);
 TOES[s]=[];
 for(let i=0;i<3;i++){const x=-s*.014+s*i*.0135,r=i==0?.009:.0076-i*.0004,b0=add(A,[x,-.032,.074]),m=add(b0,[s*.001,.002,.018-i*.002]),tip=add(m,[s*.001,-.008,.016-i*.002]);
  Cc(add(A,[x*.6,-.014,.03]),b0,.0045,.0055,ft,.003);E(b0,[r*1.15,r*1.05,r*1.1],ft,.003);Cc(b0,m,r,r*.86,ft,.002);E(m,[r*1.05,r*1.0,r*1.0],ft,.0015);E(add(m,[0,-.002,-.001]),[r*.8,r*.35,r*.6],ft,.001,null,1);Cc(m,tip,r*.86,r*.7,ft,.0015);TOES[s].push([tip,r*.7])}
 E(add(A,[s*.026,-.03,.036]),[.008,.008,.012],ft,.004);TOES[s].push([add(A,[s*.03,-.034,.046]),.005]);
}
// boyun + iri baş
Cc([0,.54,.035],[0,.61,.075],.028,.026,2,.02);
const HC=J[3];
E(add(HC,[0,.026,-.012]),[.104,.077,.088],3,.02);
E(add(HC,[0,-.032,.035]),[.09,.043,.06],3,.018);
E(add(HC,[0,-.062,.068]),[.03,.02,.022],3,.01);
E(add(HC,[0,.038,.07]),[.086,.015,.022],3,.008);
for(const s of[-1,1]){
 E(add(HC,[s*.062,0,.058]),[.036,.023,.026],3,.01);
 E(add(HC,[s*.04,.02,.08]),[.021,.017,.016],3,.005,null,1);
 E(add(HC,[s*.041,.035,.082]),[.023,.008,.014],3,.005);
 E(add(HC,[s*.04,.005,.083]),[.02,.006,.012],3,.005);
 // uzun sivri kulaklar
 Cc(add(HC,[s*.09,.02,-.012]),add(HC,[s*.215,.075,-.07]),.03,.004,3,.012);
 Cc(add(HC,[s*.104,.02,.0]),add(HC,[s*.195,.064,-.052]),.013,.002,3,.006,1);
 E(add(HC,[s*.036,.05,.074]),[.026,.006,.01],3,.003,[nrm([1,-s*.5,0]),nrm([s*.5,1,0]),[0,0,1]]);
}
// çengel burun
for(const y of[.06,.072])E(add(HC,[0,y,.074-(y-.06)*.6]),[.05,.0018,.012],3,.002,null,1);
for(const s of[-1,1])Cc(add(HC,[s*.022,-.005,.104]),add(HC,[s*.05,-.038,.088]),.0022,.0018,3,.002,1);
Cc(add(HC,[0,.03,.088]),add(HC,[0,-.014,.142]),.014,.01,3,.006);
E(add(HC,[0,-.022,.14]),[.013,.013,.012],3,.005);
Cc(add(HC,[0,-.022,.146]),add(HC,[0,-.038,.138]),.008,.005,3,.004);
for(const s of[-1,1])E(add(HC,[s*.008,-.026,.144]),[.004,.004,.005],3,.002,null,1);
// geniş sırıtış
E(add(HC,[0,-.04,.09]),[.06,.006,.03],3,.004,null,1);
E(add(HC,[0,-.034,.096]),[.054,.006,.012],3,.004);
for(const p of PR){let lo,hi,m=(p.k||0)+.02;if(p.t=='e'){const r=Math.max(...p.r);lo=sub(p.c,[r,r,r]);hi=add(p.c,[r,r,r])}else{const r=Math.max(p.r1,p.r2);lo=[Math.min(p.a[0],p.b2[0])-r,Math.min(p.a[1],p.b2[1])-r,Math.min(p.a[2],p.b2[2])-r];hi=[Math.max(p.a[0],p.b2[0])+r,Math.max(p.a[1],p.b2[1])+r,Math.max(p.a[2],p.b2[2])+r]}p.lo=sub(lo,[m,m,m]);p.hi=add(hi,[m,m,m])}
function pd(p,q){if(p.t=='e'){const d=sub(q,p.c),R=p.R;return sdEll([dot(d,R[0]),dot(d,R[1]),dot(d,R[2])],p.r)}return sdRC(q,p.a,p.b2,p.r1,p.r2)}
const inB=(p,q)=>q[0]>=p.lo[0]&&q[0]<=p.hi[0]&&q[1]>=p.lo[1]&&q[1]<=p.hi[1]&&q[2]>=p.lo[2]&&q[2]<=p.hi[2];
function sdf(q){let d=1e9;for(const p of PR)if(!p.sub&&inB(p,q))d=smin(d,pd(p,q),p.k);for(const p of PR)if(p.sub&&inB(p,q))d=-smin(-d,pd(p,q),p.k);return d}
/* --- yüzey ağları (surface nets) --- */
function buildMesh(){const h=.0043,X0=-.42,Y0=-.01,Z0=-.2,nx=Math.ceil(.84/h)+1,ny=Math.ceil(1.0/h)+1,nz=Math.ceil(.42/h)+1,F=new Float32Array(nx*ny*nz).fill(1e9),I=(i,j,k)=>(k*ny+j)*nx+i;
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
 const SKC=hx('#40641a'),PAN=hx('#45301d'),BOOT=hx('#3a2412');
 for(let v=0;v<nv;v++){const q=[P[v*3],P[v*3+1],P[v*3+2]];
  const g=nrm([sdf(add(q,[e,0,0]))-sdf(sub(q,[e,0,0])),sdf(add(q,[0,e,0]))-sdf(sub(q,[0,e,0])),sdf(add(q,[0,0,e]))-sdf(sub(q,[0,0,e]))]);N.set(g,v*3);
  let ao=0;for(const[dd,w]of[[.008,.6],[.02,.35],[.045,.2]]){ao+=w*Math.max(0,dd-sdf(add(q,mulS(g,dd))))/dd}AM[v*2]=Math.max(.25,1-ao*.9);
  const bw=new Float32Array(NB);let dmin=1e9;const ds=[];for(const p of PR){if(p.sub||!inB(p,q))continue;const d=pd(p,q);ds.push([p.b,d]);dmin=Math.min(dmin,d)}for(const[b,d]of ds)bw[b]+=Math.exp(-Math.max(0,d-dmin)/.011);
  const ord=[...bw.keys()].sort((a,b)=>bw[b]-bw[a]).slice(0,4);let tw=0;for(const o of ord)tw+=bw[o];for(let n=0;n<4;n++){BI[v*4+n]=ord[n];BW[v*4+n]=tw?bw[ord[n]]/tw:(n?0:1)}
  const ax=Math.abs(q[0]);let col=SKC,mat=1;if(q[1]<.355&&q[1]>.27&&ax<.1){col=PAN;mat=0}
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
(()=>{const HC2=J[3],LEA='#4a3020',LED='#2e1d12',RUST='#6a4a32',BONE='#d9cfb4',BRASS='#b08a3a';
 // gözler, dişler, küpe
 rg(3,()=>{for(const s of[-1,1]){const E0=add(HC2,[s*.04,.02,.075]);sp(E0,[.018,.016,.014],'#3a2a08');sp(add(E0,[0,0,.005]),[.0135,.0125,.011],'#e8b81a',{em:.7});sp(add(E0,[0,0,.0145]),[.0024,.0095,.0022],'#0a0502');sp(add(E0,[-s*.005,.005,.0148]),[.002,.002,.0014],'#fff6d0',{em:1});
   seg(add(HC2,[s*.16,.045,-.04]),add(HC2,[s*.16,.035,-.04]),.009,.009,BRASS,{met:1,nocap:1})}
  for(let i=-4;i<=4;i++){if(i==0)continue;const x=i*.0115,z=.098-Math.abs(i)*.003;cone(add(HC2,[x,-.035,z]),add(HC2,[x*1.02,-.046-(i%2?.004:0),z+.002]),.0042,'#e8dcb0')}
  for(const s of[-1,1])cone(add(HC2,[s*.038,-.044,.086]),add(HC2,[s*.041,-.024,.088]),.005,'#e8dcb0');
 });
 // kemik kolye
 rg(1,()=>{let pr=null;for(let i=0;i<=16;i++){const a=-1.2+i/16*2.4,p=[Math.sin(a)*.07,.53-Math.cos(a)*.008-(1-Math.abs(a)/1.2)*.03,.03+Math.cos(a)*.05];if(pr)seg(pr,p,.0025,.0025,LED,{nocap:1});pr=p;if(i%3==1)cone(p,add(p,[0,-.025,.006]),.0055,BONE)}
  // çapraz kayış ve kese
  seg([-.1,.53,.04],[.07,.35,.054],.008,.008,LEA,{nocap:1});seg([-.1,.53,-.045],[.07,.35,-.045],.008,.008,LEA,{nocap:1});
 });
 rg(0,()=>{// kemer ve paçavra peştamal
  let pr=null;for(let i=0;i<=24;i++){const a=i/24*2*PI,p=[Math.sin(a)*.07,.355+Math.sin(a*3)*.002,.004+Math.cos(a)*.058];if(pr)seg(pr,p,.008,.008,LEA,{nocap:1});pr=p}
  box([0,.358,.064],[.012,.012,.006],BRASS,{met:1});
  {// önde tek parça, kenarı düzensiz deri peştamal
   const NU=14,NV=12,v=[],nv=[],ix=[],hs=n=>{const q=Math.sin(n*91.3+7.7)*43758.5453;return q-Math.floor(q)};
   const bot=i=>{const u=i/(NU-1)*2-1;return .215+.02*u*u+(hs(i)-.5)*.022+(i%3==1?.012:0)};
   for(let i=0;i<NU;i++){const u=i/(NU-1)*2-1,yb=bot(i);for(let j=0;j<NV;j++){const t=j/(NV-1),y=.352+(yb-.352)*t,w=.05+.012*t,x=u*w,z=.062+.012*(1-u*u)+t*t*.012-u*u*.01+Math.sin(u*5+t*4)*.0015;v.push(x,y,z);nv.push(...nrm([u*.4,.1,1]))}}
   for(let i=0;i<NU-1;i++)for(let j=0;j<NV-1;j++){const a=i*NV+j,b=a+NV;ix.push(a,b,a+1,b,b+1,a+1)}
   it(mk(v,nv,ix),basis([1,0,0],[0,1,0],[0,0,1],[0,0,0]),'#5a4228');
   for(let k=-2;k<=2;k++)seg([k*.02,.345,.07],[k*.02,.338,.071],.0028,.0028,LED,{nocap:1});
   let pr=null;for(let i=0;i<NU;i++){const u=i/(NU-1)*2-1,q=[u*.06,bot(i)+.004,.075+.012*(1-u*u)];if(pr)seg(pr,q,.0018,.0018,'#3a2616',{nocap:1});pr=q}}box([0,.3,-.058],[.05,.055,.006],'#4a3420',{R:[[1,0,0],nrm([0,1,-.12]),nrm([0,.12,1])]});
  sp([.074,.325,.04],[.02,.024,.015],LEA);seg([.074,.348,.04],[.074,.353,.04],.011,.009,LED,{nocap:1});
 });
 // tırnaklar
 for(const s of[-1,1]){rg(bi(s,8),()=>{for(const[p,d]of TIPS[s]){const m=add(p,mulS(d,.008)),dn=nrm(add(d,[0,-.5,.25]));seg(p,m,.0042,.0034,'#2a2216',{nocap:1});cone(m,add(m,mulS(dn,.011)),.0034,'#1c160e')}
   for(let k=0;k<3;k++)seg(add(WR(s),[0,.03-k*.012,0]),add(WR(s),[0,.024-k*.012,0]),.024,.024,LED,{nocap:1})});
  rg(bi(s,14),()=>{for(const[p,r]of TOES[s]){const m=add(p,[0,-.001,.007]);seg(p,m,r*.8,r*.68,'#2a2216',{nocap:1});cone(m,add(m,[0,-.009,.009]),r*.68,'#1c160e')}});
  rg(bi(s,12),()=>{const A=AN(s);for(let k=0;k<2;k++)seg(add(A,[0,.02+k*.012,0]),add(A,[0,.028+k*.012,0]),.023,.023,LED,{nocap:1})})}
})();
/* --- kemik animasyonu --- */
const Tm=v=>new Float32Array([1,0,0,0,0,1,0,0,0,0,1,0,v[0],v[1],v[2],1]),rX=a=>{const c=Math.cos(a),s=Math.sin(a);return new Float32Array([1,0,0,0,0,c,s,0,0,-s,c,0,0,0,0,1])},rZ=a=>{const c=Math.cos(a),s=Math.sin(a);return new Float32Array([c,s,0,0,-s,c,0,0,0,0,1,0,0,0,0,1])},rYm=a=>rotY(a);
function pose(ph,walking,t,seed,dt_){const R=[];for(let b=0;b<NB;b++)R[b]=new Float32Array([1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1]);let bob=0;
 const sm=x=>{x=Math.min(1,Math.max(0,x));return x*x*(3-2*x)},hs=n=>{const v=Math.sin(n*127.1+seed*311.7)*43758.5453;return v-Math.floor(v)},lerp=(a,b,u)=>a+(b-a)*u;
 const dead=dt_!==undefined&&dt_!==null;const wk=walking?1:0;
 if(!dead){
  /* bacaklar */
  for(const s of[-1,1]){const p=ph+(s>0?0:PI),a=Math.sin(p)*.42*wk,kb=(.3+.62*Math.max(0,Math.cos(p)))*wk+.25*(1-wk);R[bi(s,10)]=rX(-a-.18);R[bi(s,12)]=rX(kb);R[bi(s,14)]=rX(a*.85-kb*.85)}
  bob=(-Math.abs(Math.sin(ph))*.012+.006)*wk;
  /* gövde */
  R[0]=mmul(rYm(Math.sin(ph)*.07*wk),rZ(Math.sin(ph)*.03*wk));
  /* satır sallama: rastgele aralıklarla tepeden vuruş ya da yandan savurma */
  const per=2.4,k=Math.floor((t+seed*9)/per),st=k*per-seed*9,on=false,off=.15+hs(k+.5)*(per-1.1),u=on?(t-st-off)/.95:-1,typ=hs(k+.25)<.55?0:1;
  const fwdR=-Math.sin(ph)*wk;// sağ kol bacağa karşı salınır
  let sh=-.32-fwdR*.1,sz=.1,el=-1.227+Math.sin(ph-.4)*.173,wr=.05+Math.sin(ph-.8)*.06,ch=0;
  if(u>0&&u<1){const K=typ==0?[[-2.45,.28,-1.95,-.45,-.22],[-.5,.04,-.2,.4,.32]]:[[-1.25,.95,-.95,.05,-.5],[-1.15,-.55,-.3,.25,.55]];
   const w=sm(u/.38),x=sm((u-.42)/.16),r=sm((u-.68)/.32);const base=[sh,sz,el,wr,ch];const v=base.map((b,i)=>{let a=lerp(b,K[0][i],w);a=lerp(a,K[1][i],x);return lerp(a,b,r)});[sh,sz,el,wr,ch]=v}
  R[1]=mmul(rYm(-Math.sin(ph)*.12+ch),rX(.2+Math.abs(ch)*.12));R[2]=rX(-.1);R[3]=rX(Math.sin(ph*2)*.05-ch*.15-.12);
  R[5]=mmul(rX(sh),rZ(sz));R[7]=rX(el);R[9]=mmul(rX(wr),rZ(-.05));
  /* sol kol: omuz-dirsek-bilek aynı ritimde, dirsek gecikmeli kırılır */
  const fwdL=Math.sin(ph)*wk,lag=Math.sin(ph-.45)*wk,lag2=Math.sin(ph-.9)*wk;
  R[4]=mmul(rX(-fwdL*.46-ch*.4),rZ(-.13-Math.abs(fwdL)*.03));
  R[6]=rX(-.536-Math.max(0,lag)*.622-Math.max(0,-lag)*.104);
  R[8]=mmul(rX(-.08-lag2*.18),rZ(lag2*.06));
  for(const s of[-1,1]){const fw=(s<0?Math.sin(ph):-Math.sin(ph))*wk,lag=(s<0?Math.sin(ph-.35):-Math.sin(ph-.35))*wk,lag2=(s<0?Math.sin(ph-.7):-Math.sin(ph-.7))*wk,br=Math.sin(t*1.6+(s>0?.8:0))*(1-wk)*.05;
   R[bi(s,4)]=mmul(rX(-fw*.42+.05+br),rZ(-s*.2));R[bi(s,6)]=rX(-(.42+.32*(lag+1)/2)-br*.6);R[bi(s,8)]=mmul(rX(-.1-.14*lag2-br*.5),rZ(s*.04*lag2))}
 }else{
  /* ölüm: darbeyle sarsılır, dizleri çözülür, yana yığılıp düşer, gevşer ve kaybolur */
  const d=dt_,b=sm(d/.07)*(1-sm((d-.08)/.14)),k=sm((d-.04)/.3),lp=sm((d-.38)/.25),side=hs(3)<.5?-1:1;
  for(const s of[-1,1]){const kk=s==side?1.1:.85;R[bi(s,10)]=rX(-.25*b-.55*k*kk+.35*lp);R[bi(s,12)]=rX(.25*b+1.25*k*kk-.6*lp);R[bi(s,14)]=rX(-.15*b-.45*k+.3*lp)}
  R[0]=mmul(rZ(side*.08*k),rX(-.08*b));
  R[1]=mmul(rX(-.32*b+.3*k-.12*lp),rZ(side*.12*k));R[2]=rX(-.15*b+.1*k);R[3]=mmul(rX(-.55*b+.35*k-.15*lp),rZ(side*.35*lp));
  for(const s of[-1,1]){const out=s==side?1:.6;R[bi(s,4)]=mmul(rX(-.55*b-.25*k-.7*lp*out),rZ(s*(.55*b+.25*k+.55*lp*out)));R[bi(s,6)]=rX(-.35*b-.5*k+.25*lp);R[bi(s,8)]=rX(.3*k)}
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
 const H=heightOf(e)*(e.k=='goblin'?1.48:1);let X=e.c-N/2,Z=e.r,side_;if(dead&&e.kb){const k=.42*(1-Math.pow(1-Math.min(1,ct/.32),3));let nx=e.c+e.kb[0]*k,nz=e.r+e.kb[1]*k;if(typeof pathPos=='function'&&e.s!==undefined){const c0=pathPos(e.s,0),dx=nx-c0[0],dz=nz-c0[1],dl=Math.hypot(dx,dz);if(dl>.42){nx=c0[0]+dx/dl*.42;nz=c0[1]+dz/dl*.42}}X=nx-N/2;Z=nz;const a_=e.hc||0;side_=(-Math.cos(a_)*e.kb[0]+Math.sin(a_)*e.kb[1])>=0?1:-1}
 if(e.cs===undefined)e.cs=Math.random();const q={side:side_,sd:e.cs,X,Z,H,a:e.hc,ph:e.ph||0,dead,ct,fl:!dead&&e.fl>0?1:0,slow:!dead&&e.slow>0,w:(e.wob||0)*3};
 q.S=pose(dead?0:q.ph,!dead,time+q.sd*50,q.sd,dead?ct:null);q.R=rootM(q);
 if(!dead){
  for(const s of[-1,1]){const fp=xf(mmul(q.R,q.S[bi(s,14)]),add(AN(s),[0,-.05,.04])),hh=Math.max(0,fp[1]),al=.85*Math.max(0,1-hh/(.06*H)),r=.06*H*(1+hh/(.1*H));if(al>.02)prim(GD_,mT(fp[0],.022,fp[2]),[r,1,r],[0,0,0],0,al)}}
 QU.push(q);return H}
function rootM(q){const S=q.H,sc=new Float32Array([S,0,0,0,0,S,0,0,0,0,S,0,0,0,0,1]);let M=mmul(Tm([q.X,0,q.Z]),rotY(q.a));
 if(q.dead){const ct=q.ct,hv=Math.sin(q.sd*311.7)*43758.5453,side=q.side||((hv-Math.floor(hv))<.5?-1:1),f=Math.min(1,Math.max(0,(ct-.1)/.34)),fe=f*f*(1.6-.6*f),tb=ct-.44,bn=tb>0?Math.sin(tb*16)*Math.exp(-tb*7)*.08:0,kick=ct<.18?Math.sin(ct/.18*PI)*.04:0,sink=Math.max(0,ct-.95)/.5;
  M=mmul(Tm([q.X,(fe*.05-sink*.6)*q.H,q.Z]),mmul(rotY(q.a+side*fe*.35),mmul(Tm([side*.05*q.H,0,-kick*q.H]),mmul(rZ(side*(fe*PI*.46-bn)),Tm([-side*.05*q.H,0,0])))))}
 return mmul(M,sc)}
function daggerM(q,S_,R_){const RL=.2;if(!(q.dead&&q.ct>RL))return null;const SC=q.H,Sr=pose(0,false,0,q.sd,RL),Rb=rootM(Object.assign({},q,{ct:RL})),Mr=mmul(Rb,Sr[9]),gw=xf(Mr,add(WR(1),[0,-.032,.006])),loc=mmul(Tm([-gw[0],-gw[1],-gw[2]]),Mr);
 const t=q.ct-RL,vy=3.1*SC,vx=.55*SC,vz=-.25*SC,yEnd=.16*SC,tl=(vy+Math.sqrt(vy*vy+19.6*Math.max(0,gw[1]-yEnd)))/9.8;
 if(t<tl)return mmul(Tm([gw[0]+vx*t,gw[1]+vy*t-4.9*t*t,gw[2]+vz*t]),mmul(rX(t*17),loc));
 const w=t-tl,wob=Math.sin(w*34)*Math.exp(-w*5)*.35;return mmul(Tm([gw[0]+vx*tl,yEnd,gw[2]+vz*tl]),mmul(rZ(wob),mmul(rX(PI+.3),loc)))}
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
  const pp=depth?DP:PP;setU(pp);
  const CLM=daggerM(q),SHM=null;
  const list=GRP.map(o=>({g:o,M:(CLM&&o.cl)?CLM:(SHM&&o.shd)?SHM:mmul(R,S[o.b]),c:o.c,e:o.e,m:o.m,u32:1}));
  const cf0=q.dead?Math.min(1,Math.max(0,(q.ct-1.55)/.45)):0,cf=cf0*cf0*(3-2*cf0),CS=new Float32Array([1,0,0,0,0,1-.25*cf,0,0,0,0,1-.82*cf,0,0,.03*cf,.02*cf,1]);
  
  if(false){
   }
  for(const d of list){gl.uniformMatrix4fv(pp.u.M,false,d.M);gl.uniformMatrix3fv(pp.u.NM,false,nmat(d.M));if(!depth){gl.uniform3fv(pp.u.col,q.slow?[d.c[0]*.75,d.c[1]*.9,Math.min(1,d.c[2]*1.3+.08)]:d.c);gl.uniform1f(pp.u.em,d.e);gl.uniform1f(pp.u.met,d.m);gl.uniform1f(pp.u.kind,0)}gl.bindVertexArray(d.g.vao);gl.drawElements(gl.TRIANGLES,d.g.n,d.u32?gl.UNSIGNED_INT:gl.UNSIGNED_SHORT,0)}
 }
 gl.bindVertexArray(null);if(cull)gl.enable(gl.CULL_FACE);if(!depth)QU.length=0}
return{queue,pass,verts:MESH.nv};

}catch(err){console.error('Goblin modülü yüklenemedi',err);return undefined}})();
