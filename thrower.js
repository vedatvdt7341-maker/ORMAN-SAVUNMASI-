/* Kale Nöbeti · Ork Şefi: tek parça iskeletli deri (oyuna bağlanan modül) */
const THR=(()=>{try{
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
/* --- iskelet (insan köylü, ~0.92 boy) --- */
const J=[[0,.47,0],[0,.6,.005],[0,.7,.01],[0,.79,.02]];const PAR=[-1,0,1,2];
const SH=s=>[s*.15,.672,0],EL=s=>[s*.172,.52,-.012],WR=s=>[s*.182,.378,.012],HP=s=>[s*.075,.462,0],KN=s=>[s*.083,.258,.012],AN=s=>[s*.088,.058,-.012];
J[4]=SH(-1);J[5]=SH(1);J[6]=EL(-1);J[7]=EL(1);J[8]=WR(-1);J[9]=WR(1);J[10]=HP(-1);J[11]=HP(1);J[12]=KN(-1);J[13]=KN(1);J[14]=AN(-1);J[15]=AN(1);
PAR[4]=1;PAR[5]=1;PAR[6]=4;PAR[7]=5;PAR[8]=6;PAR[9]=7;PAR[10]=0;PAR[11]=0;PAR[12]=10;PAR[13]=11;PAR[14]=12;PAR[15]=13;
const NB=16,bi=(s,base)=>base+(s>0?1:0),TIPS={},TOES={};
const PR=[];
function E(c,r,b,k,ax,sub){const R=ax||[[1,0,0],[0,1,0],[0,0,1]];PR.push({t:'e',c,r,R,b,k,sub})}
function Cc(a,bb,r1,r2,b,k,sub){PR.push({t:'c',a,b2:bb,r1,r2,b,k,sub})}
function Ealong(A,B,t,rx,ry,rz,off,b,k){const d=nrm(sub(B,A)),[x,z]=frame(d,[0,0,1]);E(add(lerp(A,B,t),off),[rx,ry,rz],b,k,[x,d,z])}
// gövde
E([0,.47,0],[.108,.06,.075],0,.03);
E([0,.535,.008],[.098,.065,.068],0,.03);
E([0,.612,.01],[.122,.07,.078],1,.03);
E([0,.632,-.032],[.118,.058,.05],1,.03);
for(const s of[-1,1]){E([s*.05,.625,.055],[.055,.038,.028],1,.016);E([s*.068,.688,-.012],[.06,.024,.04],1,.02);E([s*.05,.69,.04],[.05,.012,.016],1,.012)}
for(const s of[-1,1]){
 const S=SH(s),El=EL(s),W=WR(s),ua=bi(s,4),fa=bi(s,6),hd=bi(s,8);
 E(add(S,[s*.01,.002,0]),[.046,.044,.046],ua,.02);
 Cc(S,El,.037,.03,ua,.018);
 Ealong(S,El,.5,.04,.068,.036,[0,0,.012],ua,.012);
 Ealong(S,El,.45,.036,.07,.032,[s*.004,0,-.014],ua,.012);
 E(add(El,[0,.002,-.018]),[.016,.016,.014],fa,.008);
 Cc(El,W,.031,.021,fa,.014);
 Ealong(El,W,.32,.036,.065,.031,[s*.006,0,.004],fa,.012);
 // el: avuç, başparmak, dört parmak (üç boğum)
 Cc(add(W,[0,.008,0]),add(W,[0,-.014,.002]),.022,.021,hd,.008);
 E(add(W,[s*.002,-.034,.004]),[.026,.035,.0135],hd,.008);
 E(add(W,[-s*.004,-.03,.016]),[.014,.018,.01],hd,.006);
 TIPS[s]=[];const curl=s>0?.42:.3;
 for(let i=0;i<4;i++){const z=-.017+i*.0115,lenF=[.92,1.05,1,.8][i],rr=[.0068,.0072,.0068,.006][i];let p=add(W,[s*.002,-.066,z]);E(p,[.0085,.008,.0085],hd,.003);
  let d=[0,-1,0];const segL=[.026,.018,.014].map(x=>x*lenF);
  for(let k=0;k<3;k++){d=nrm(add(d,[0,0,curl]));const n=add(p,mulS(d,segL[k]));Cc(p,n,rr*(1-k*.08),rr*(.9-k*.1),hd,.0018);if(k<2)E(n,[rr*1.08,rr*1.02,rr*1.08],hd,.0012);p=n}
  TIPS[s].push([p,d])}
 {let p=add(W,[-s*.004,-.028,.024]);let d=nrm([-s*.15,-.55,.75]);for(let k=0;k<2;k++){d=nrm(add(d,[-s*.1,-.15,.2*curl]));const n=add(p,mulS(d,.02-k*.004));Cc(p,n,.0088-k*.0012,.0078-k*.0014,hd,.0024);p=n}TIPS[s].push([p,d])}
 // bacaklar
 const Hp=HP(s),K=KN(s),A=AN(s),th=bi(s,10),cf=bi(s,12),ft=bi(s,14);
 Cc(Hp,K,.058,.04,th,.024);
 Ealong(Hp,K,.45,.058,.1,.052,[s*.004,0,.022],th,.014);
 Ealong(Hp,K,.4,.052,.095,.046,[0,0,-.02],th,.014);
 E(add(K,[0,.004,.024]),[.027,.028,.018],cf,.01);
 Cc(K,A,.038,.024,cf,.014);
 Ealong(K,A,.3,.045,.078,.04,[0,0,-.02],cf,.012);
 E(add(A,[0,-.028,.032]),[.034,.022,.078],ft,.014);
 E(add(A,[0,-.028,-.018]),[.026,.024,.03],ft,.012);
 TOES[s]=[];
}
// boyun ve baş
Cc([0,.67,.0],[0,.755,.022],.044,.04,2,.024);
E([0,.715,.04],[.012,.014,.01],2,.006);
const HC=J[3];
E(add(HC,[0,.03,-.012]),[.074,.084,.088],3,.02);
E(add(HC,[0,-.012,.034]),[.064,.066,.058],3,.02);
E(add(HC,[0,-.058,.03]),[.056,.03,.054],3,.016);
E(add(HC,[0,-.076,.058]),[.022,.018,.018],3,.01);
E(add(HC,[0,.026,.074]),[.058,.011,.016],3,.008);
for(const s of[-1,1]){
 E(add(HC,[s*.044,-.004,.06]),[.022,.016,.02],3,.01);
 E(add(HC,[s*.027,.008,.08]),[.016,.011,.012],3,.005,null,1);
 E(add(HC,[s*.028,.02,.083]),[.017,.005,.009],3,.004);
 E(add(HC,[s*.028,-.003,.084]),[.015,.004,.008],3,.004);
 E(add(HC,[s*.074,0,-.002]),[.01,.027,.019],3,.006);
 E(add(HC,[s*.081,0,.0]),[.005,.017,.011],3,.003,null,1);
 E(add(HC,[s*.012,-.031,.098]),[.008,.006,.008],3,.004);
 E(add(HC,[s*.03,-.052,.078]),[.008,.006,.008],3,.004,null,1);
}
Cc(add(HC,[0,.02,.085]),add(HC,[0,-.019,.104]),.0105,.0115,3,.006);
E(add(HC,[0,-.024,.104]),[.012,.011,.011],3,.005);
for(const s of[-1,1])E(add(HC,[s*.007,-.031,.1]),[.0035,.0028,.004],3,.0015,null,1);
E(add(HC,[0,-.044,.088]),[.022,.0062,.011],3,.004);
E(add(HC,[0,-.056,.086]),[.02,.0072,.011],3,.004);
E(add(HC,[0,-.05,.096]),[.022,.0016,.008],3,.0015,null,1);
for(const p of PR){let lo,hi,m=(p.k||0)+.02;if(p.t=='e'){const r=Math.max(...p.r);lo=sub(p.c,[r,r,r]);hi=add(p.c,[r,r,r])}else{const r=Math.max(p.r1,p.r2);lo=[Math.min(p.a[0],p.b2[0])-r,Math.min(p.a[1],p.b2[1])-r,Math.min(p.a[2],p.b2[2])-r];hi=[Math.max(p.a[0],p.b2[0])+r,Math.max(p.a[1],p.b2[1])+r,Math.max(p.a[2],p.b2[2])+r]}p.lo=sub(lo,[m,m,m]);p.hi=add(hi,[m,m,m])}
function pd(p,q){if(p.t=='e'){const d=sub(q,p.c),R=p.R;return sdEll([dot(d,R[0]),dot(d,R[1]),dot(d,R[2])],p.r)}return sdRC(q,p.a,p.b2,p.r1,p.r2)}
const inB=(p,q)=>q[0]>=p.lo[0]&&q[0]<=p.hi[0]&&q[1]>=p.lo[1]&&q[1]<=p.hi[1]&&q[2]>=p.lo[2]&&q[2]<=p.hi[2];
function sdf(q){let d=1e9;for(const p of PR)if(!p.sub&&inB(p,q))d=smin(d,pd(p,q),p.k);for(const p of PR)if(p.sub&&inB(p,q))d=-smin(-d,pd(p,q),p.k);return d}
/* --- yüzey ağları (surface nets) --- */
function buildMesh(){const h=.0052,X0=-.42,Y0=-.01,Z0=-.2,nx=Math.ceil(.84/h)+1,ny=Math.ceil(1.0/h)+1,nz=Math.ceil(.42/h)+1,F=new Float32Array(nx*ny*nz).fill(1e9),I=(i,j,k)=>(k*ny+j)*nx+i;
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
 const SKC=hx('#c98e68'),PAN=hx('#5a4630'),SHT=hx('#c9b48a'),BOOT=hx('#3a2412');
 for(let v=0;v<nv;v++){const q=[P[v*3],P[v*3+1],P[v*3+2]];
  const g=nrm([sdf(add(q,[e,0,0]))-sdf(sub(q,[e,0,0])),sdf(add(q,[0,e,0]))-sdf(sub(q,[0,e,0])),sdf(add(q,[0,0,e]))-sdf(sub(q,[0,0,e]))]);N.set(g,v*3);
  let ao=0;for(const[dd,w]of[[.008,.6],[.02,.35],[.045,.2]]){ao+=w*Math.max(0,dd-sdf(add(q,mulS(g,dd))))/dd}AM[v*2]=Math.max(.25,1-ao*.9);
  const bw=new Float32Array(NB);let dmin=1e9;const ds=[];for(const p of PR){if(p.sub||!inB(p,q))continue;const d=pd(p,q);ds.push([p.b,d]);dmin=Math.min(dmin,d)}for(const[b,d]of ds)bw[b]+=Math.exp(-Math.max(0,d-dmin)/.011);
  const ord=[...bw.keys()].sort((a,b)=>bw[b]-bw[a]).slice(0,4);let tw=0;for(const o of ord)tw+=bw[o];for(let n=0;n<4;n++){BI[v*4+n]=ord[n];BW[v*4+n]=tw?bw[ord[n]]/tw:(n?0:1)}
  const ax=Math.abs(q[0]);let col=SKC,mat=1;if(q[1]<.455&&q[1]>.07&&!(ax>.16&&q[1]>.3)){col=PAN;mat=0}else if(q[1]>=.455&&q[1]<.69&&!(ax>.15&&q[1]<.5)&&!(q[1]>.66&&ax<.05&&q[2]>.0)){col=SHT;mat=0}
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
(()=>{const HC2=J[3],HAIR='#3a2618',ROPE='#b08850',ROPD='#7a5a30',LEA='#6a4626',LED='#3e2614',SHOE='#4a3220',STONE='#8a8a86';
 rg(3,()=>{for(const s of[-1,1]){const E0=add(HC2,[s*.027,.008,.074]);sp(E0,[.0115,.0115,.011],'#eee8de');sp(add(E0,[0,0,.009]),[.0062,.0062,.003],'#5a3a1e');sp(add(E0,[0,0,.0108]),[.003,.003,.0015],'#0a0604');sp(add(E0,[-s*.002,.002,.0115]),[.0012,.0012,.0008],'#ffffff',{em:1});
   seg(add(HC2,[s*.012,.031,.084]),add(HC2,[s*.044,.034,.074]),.0045,.0032,HAIR,{nocap:1})}
  sp(add(HC2,[0,.052,-.016]),[.079,.064,.085],HAIR);sp(add(HC2,[0,.036,-.05]),[.077,.062,.06],HAIR);
  for(const s of[-1,1])sp(add(HC2,[s*.066,.02,-.02]),[.016,.035,.04],HAIR);
  for(let i=0;i<7;i++){const x=(i-3)*.02;sp(add(HC2,[x,.074+Math.sin(i*1.7)*.004,.05-Math.abs(x)*.3]),[.016,.01,.02],HAIR)}
  sp(add(HC2,[0,-.04,.093]),[.024,.006,.006],HAIR);
 });
 // yaka
 rg(1,()=>{let pr=null;for(let i=0;i<=20;i++){const a=i/20*2*PI,p=[Math.sin(a)*.052,.692+Math.cos(a)*.008,.008+Math.cos(a)*.044];if(pr)seg(pr,p,.0065,.0065,'#b8a07a',{nocap:1});pr=p}
  seg([-.012,.68,.052],[0,.64,.07],.003,.003,'#8a7050',{nocap:1});seg([.012,.68,.052],[0,.64,.07],.003,.003,'#8a7050',{nocap:1})});
 // ip kuşak, düğüm ve kese
 rg(0,()=>{for(const dy of[0,.012]){let pr=null;for(let i=0;i<=28;i++){const a=i/28*2*PI,p=[Math.sin(a)*.112,.462+dy+Math.sin(a*5)*.0015,.002+Math.cos(a)*.078];if(pr)seg(pr,p,.0068,.0068,i%2?ROPE:ROPD,{nocap:1});pr=p}}
  const kn=[-.04,.468,.078];sp(kn,[.012,.011,.009],ROPE);seg(kn,[-.046,.41,.08],.005,.004,ROPE);seg(kn,[-.03,.405,.082],.005,.004,ROPE);sp([-.046,.406,.08],[.006,.007,.006],ROPD);sp([-.03,.401,.082],[.006,.007,.006],ROPD);
  const pc=[.104,.405,.035];seg([.104,.46,.04],add(pc,[0,.03,0]),.004,.004,ROPD,{nocap:1});
  sp(pc,[.026,.032,.022],LEA);sp(add(pc,[0,.026,0]),[.02,.008,.017],LED);seg(add(pc,[-.014,.03,.01]),add(pc,[-.02,.012,.02]),.0022,.0018,ROPE,{nocap:1});
  for(const k of[-1,1])sp(add(pc,[k*.008,.034,.004]),[.007,.006,.007],'#55554f')});
 // ayakkabılar
 for(const s of[-1,1]){rg(bi(s,14),()=>{const A=AN(s);sp(add(A,[0,-.026,.03]),[.04,.027,.088],SHOE);sp(add(A,[0,-.024,-.018]),[.032,.03,.034],SHOE);box(add(A,[0,-.052,.03]),[.038,.005,.088],'#2a1a10');
   seg(add(A,[0,.004,.0]),add(A,[0,.03,-.004]),.036,.037,SHOE,{nocap:1});for(let k=0;k<3;k++)seg(add(A,[-.03,-.004,.02+k*.02]),add(A,[.03,-.004,.02+k*.02]),.0025,.0025,LED,{nocap:1,rz:.5})});
  rg(bi(s,8),()=>{for(const[p,d]of TIPS[s])sp(add(p,mulS(d,-.002)),[.0045,.002,.004],'#d8b0a0')})}
 // sırtta taş dolu deri çanta ve askıları
 rg(1,()=>{const BG=[0,.585,-.108];sp(BG,[.085,.1,.052],LEA);sp(add(BG,[0,-.07,.0]),[.078,.04,.048],LED);
  let pr=null;for(let i=0;i<=18;i++){const a=i/18*2*PI,p=add(BG,[Math.sin(a)*.07,.088,Math.cos(a)*.042]);if(pr)seg(pr,p,.008,.008,LED,{nocap:1});pr=p}
  const ST=[[-.035,.1,.0,.024],[.0,.115,-.01,.028],[.035,.1,.008,.023],[-.012,.098,.022,.02],[.022,.12,-.024,.021],[-.03,.112,-.022,.018]];
  for(const[x,y,z,r]of ST)sp(add(BG,[x,y,z]),[r,r*.85,r*.95],x>0?'#55554f':'#4a4a46');
  for(const s of[-1,1]){seg(add(BG,[s*.05,.08,.03]),[s*.075,.69,.0],.009,.009,LED,{nocap:1});seg([s*.075,.69,.0],[s*.085,.66,.06],.009,.009,LED,{nocap:1});seg([s*.085,.66,.06],[s*.1,.545,.06],.009,.009,LED,{nocap:1});seg([s*.1,.545,.06],add(BG,[s*.07,-.08,.03]),.008,.008,LED,{nocap:1});sp([s*.1,.6,.07],[.008,.008,.004],'#b8963a',{met:1})}
  box(add(BG,[0,.03,.05]),[.05,.05,.004],LED,{R:[[1,0,0],nrm([0,1,-.15]),nrm([0,.15,1])]})});
})();
/* --- kemik animasyonu --- */
const Tm=v=>new Float32Array([1,0,0,0,0,1,0,0,0,0,1,0,v[0],v[1],v[2],1]),rX=a=>{const c=Math.cos(a),s=Math.sin(a);return new Float32Array([1,0,0,0,0,c,s,0,0,-s,c,0,0,0,0,1])},rZ=a=>{const c=Math.cos(a),s=Math.sin(a);return new Float32Array([c,s,0,0,-s,c,0,0,0,0,1,0,0,0,0,1])},rYm=a=>rotY(a);
function pose(u,tt,seed){const R=[];for(let b=0;b<NB;b++)R[b]=new Float32Array([1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1]);
 const sm=x=>{x=Math.min(1,Math.max(0,x));return x*x*(3-2*x)};
 // iki elle atış: 0 dur, .18 iki el sırttaki çantadan taşı kavrar, .32 taşı başın üstüne kaldırır, .46 çömelip geriye kurulur, .6 zıplayıp fırlatır, .74 yere iner, 1 dur
 const KT=[0,.18,.32,.46,.6,.74,1],act=u>=0&&u<1;
 const key=v=>{if(!act)return v[0];let i=0;while(i<KT.length-2&&u>KT[i+1])i++;const f=sm((u-KT[i])/(KT[i+1]-KT[i]));return v[i]+(v[i+1]-v[i])*f};
 const br=Math.sin(tt*1.7+seed)*.02,sw=Math.sin(tt*.6+seed*3)*.03;
 const tl=key([.02,.1,-.08,-.24,.34,.22,.02]),hip=key([0,-.05,-.08,-.55,.08,-.45,0]),kn=key([.12,.18,.2,1.05,.02,.85,.12]),an=key([0,-.02,-.08,-.45,.25,-.38,0]),hd=key([0,.28,-.22,-.18,.06,.05,0]);
 const jy=act&&u>.5&&u<.72?Math.sin((u-.5)/.22*PI)*.12:0;
 R[0]=rYm(sw*.3);
 for(const s of[-1,1]){const st=s<0?-.07:.07;R[bi(s,10)]=rX(hip+st);R[bi(s,12)]=rX(kn);R[bi(s,14)]=rX(an-st*.5)}
 R[1]=rX(tl+br);R[2]=rX(-tl*.35);R[3]=rX(-tl*.55+hd+br*.5);
 // omurga dünya matrisleri
 const W=[];for(let b=0;b<4;b++){const p=PAR[b];W[b]=p<0?mmul(Tm(J[b]),R[b]):mmul(W[p],mmul(Tm(sub(J[b],J[p])),R[b]))}
 const xp=(M,p)=>[M[0]*p[0]+M[4]*p[1]+M[8]*p[2]+M[12],M[1]*p[0]+M[5]*p[1]+M[9]*p[2]+M[13],M[2]*p[0]+M[6]*p[1]+M[10]*p[2]+M[14]];
 const xv=(M,v)=>[M[0]*v[0]+M[4]*v[1]+M[8]*v[2],M[1]*v[0]+M[5]*v[1]+M[9]*v[2],M[2]*v[0]+M[6]*v[1]+M[10]*v[2]];
 const rot=M=>new Float32Array([M[0],M[1],M[2],0,M[4],M[5],M[6],0,M[8],M[9],M[10],0,0,0,0,1]),tr=M=>new Float32Array([M[0],M[4],M[8],0,M[1],M[5],M[9],0,M[2],M[6],M[10],0,0,0,0,1]);
 const axr=(ax,a)=>{const[x,y,z]=ax,c=Math.cos(a),s_=Math.sin(a),t=1-c;return new Float32Array([t*x*x+c,t*x*y+s_*z,t*x*z-s_*y,0,t*x*y-s_*z,t*y*y+c,t*y*z+s_*x,0,t*x*z+s_*y,t*y*z-s_*x,t*z*z+c,0,0,0,0,1])};
 const rmin=(a,b)=>{a=nrm(a);b=nrm(b);const c=Math.max(-1,Math.min(1,a[0]*b[0]+a[1]*b[1]+a[2]*b[2])),ax=cross(a,b),l=Math.hypot(...ax);if(l<1e-6)return new Float32Array([1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1]);return axr(mulS(ax,1/l),Math.acos(c))};
 const loc=(Wp,d0,d1)=>{const Rp=rot(Wp);return mmul(tr(Rp),mmul(rmin(xv(Rp,d0),d1),Rp))};
 // taşın yolu (gövde uzayında) ve tutma ağırlığı
 const SP=[[0,.6,.08],[0,.83,-.12],[0,.99,-.03],[0,.94,-.12],[0,.9,.21],[0,.66,.24],[0,.6,.08]];
 const sk=i=>key(SP.map(p=>p[i])),stone=[sk(0),sk(1),sk(2)],w=act?sm((u-.04)/.12)*(1-sm((u-.66)/.14)):0,hold=act&&u>=.17&&u<.6;
 for(const s of[-1,1]){
  const ua=bi(s,4),fa=bi(s,6),hdb=bi(s,8),Sw=xp(W[1],sub(SH(s),J[1])),a=Math.hypot(...sub(EL(s),SH(s))),b=Math.hypot(...sub(WR(s),EL(s)));
  const idle=xp(W[1],sub(add(WR(s),[-s*.006,.01,.03+(s<0?br:-br)]),J[1]));
  const tg=add(stone,[s*.088,.02,-.012]),T=[idle[0]+(tg[0]-idle[0])*w,idle[1]+(tg[1]-idle[1])*w,idle[2]+(tg[2]-idle[2])*w];
  let dv=sub(T,Sw),d=Math.hypot(...dv);const dc=Math.min(a+b-.002,Math.max(Math.abs(a-b)+.002,d));dv=nrm(dv);
  const pole=nrm(sub([s*.35,-.25,-.2],mulS(dv,s*.35*dv[0]-.25*dv[1]-.2*dv[2]))),ca=(a*a+dc*dc-b*b)/(2*a*dc),sa=Math.sqrt(Math.max(0,1-ca*ca));
  const Ew=add(Sw,add(mulS(dv,a*ca),mulS(pole,a*sa))),Tw=add(Sw,mulS(dv,dc));
  R[ua]=loc(W[1],sub(EL(s),SH(s)),sub(Ew,Sw));
  const W4=mmul(W[1],mmul(Tm(sub(SH(s),J[1])),R[ua]));
  R[fa]=loc(W4,sub(WR(s),EL(s)),sub(Tw,Ew));
  const W6=mmul(W4,mmul(Tm(sub(EL(s),SH(s))),R[fa]));
  const hdir=nrm(add(mulS(nrm(sub(Tw,Ew)),1-w),mulS(nrm(sub(add(stone,[s*.03,-.004,.0]),Tw)),w)));
  R[hdb]=mmul(loc(W6,[0,-1,0.05],hdir),rZ(s*.0));
 }
 const S=[];for(let b=0;b<NB;b++){const p=PAR[b];if(b>=4)W[b]=mmul(W[p],mmul(Tm(sub(J[b],J[p])),R[b]));S[b]=mmul(W[b],Tm(mulS(J[b],-1)))}
 let minY=1e9;for(const s of[-1,1]){const w_=S[bi(s,14)];for(const a of[add(AN(s),[0,-.055,.03]),add(AN(s),[0,-.055,.1]),add(AN(s),[0,-.055,-.03])]){const y=w_[1]*a[0]+w_[5]*a[1]+w_[9]*a[2]+w_[13];minY=Math.min(minY,y)}}
 const dy=.004-minY+jy;for(let b=0;b<NB;b++)S[b]=mmul(Tm([0,dy,0]),S[b]);S.stone=[stone[0],stone[1]+dy,stone[2]];S.hold=hold;return S}
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
function queueM(Mw,sc,u,tt,seed,fl,Mp){const s=sc,Sc=new Float32Array([s,0,0,0,0,s,0,0,0,0,s,0,0,0,0,1]),R=mmul(Mw,mmul(Sc,rotY(PI/2))),S=pose(u,tt,seed||0),hold=0;
 const q={R,S,pile:true,RP:Mp?mmul(Mp,mmul(Sc,rotY(PI/2))):R,hold:S.hold,fl:fl?1:0,slow:false,dead:false,ct:0,H:1,w:0,sd:seed||0};QU.push(q);return{R,hand:xf(R,S.stone)}}
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
  const pp=depth?DP:PP;setU(pp);
  
  const list=GRP.map(o=>({g:o,M:mmul(R,S[o.b]),c:o.c,e:o.e,m:o.m,u32:1}));if(q.hold){const sp_=xf(R,S.stone),sx=Math.hypot(R[0],R[1],R[2]);list.push({g:GS,M:basis([.07*sx,0,0],[0,.06*sx,0],[0,0,.064*sx],sp_),c:[.3,.3,.29],e:0,m:0},{g:GS,M:basis([.032*sx,0,0],[0,.027*sx,0],[0,0,.03*sx],add(sp_,[.025*sx,.022*sx,.03*sx])),c:[.38,.38,.36],e:0,m:0})}if(q.pile){const PL=[[0.514,0.07,0.12,0.078],[0.465,0.068,0.219,0.081],[0.391,0.07,0.303,0.076],[0.342,0.066,0.402,0.074],[0.485,0.19,0.167,0.074],[0.432,0.195,0.264,0.077],[0.366,0.188,0.353,0.072],[0.457,0.3,0.214,0.07],[0.399,0.302,0.308,0.068]];PL.forEach(([x,y,z,r],k)=>list.push({g:GS,M:mmul(q.RP,basis([r*1.1,0,0],[0,r*.85,0],[0,0,r],[x,y,z])),c:k%3==0?[.3,.3,.29]:k%3==1?[.36,.36,.34]:[.26,.26,.25],e:0,m:0}))}
  const cf0=q.dead?Math.min(1,Math.max(0,(q.ct-1.55)/.45)):0,cf=cf0*cf0*(3-2*cf0),CS=new Float32Array([1,0,0,0,0,1-.25*cf,0,0,0,0,1-.82*cf,0,0,.03*cf,.02*cf,1]);
  

  for(const d of list){gl.uniformMatrix4fv(pp.u.M,false,d.M);gl.uniformMatrix3fv(pp.u.NM,false,nmat(d.M));if(!depth){gl.uniform3fv(pp.u.col,q.slow?[d.c[0]*.75,d.c[1]*.9,Math.min(1,d.c[2]*1.3+.08)]:d.c);gl.uniform1f(pp.u.em,d.e);gl.uniform1f(pp.u.met,d.m);gl.uniform1f(pp.u.kind,0)}gl.bindVertexArray(d.g.vao);gl.drawElements(gl.TRIANGLES,d.g.n,d.u32?gl.UNSIGNED_INT:gl.UNSIGNED_SHORT,0)}
 }
 gl.bindVertexArray(null);if(cull)gl.enable(gl.CULL_FACE);if(!depth)QU.length=0}
return{queueM,pass,verts:MESH.nv};

}catch(err){console.error('Taşçı modülü yüklenemedi',err);return undefined}})();
