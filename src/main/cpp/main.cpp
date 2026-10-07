// Nomad Animator - editor/animador 3D em C++ + OpenGL ES 3.0 (NativeActivity)
#include <android_native_app_glue.h>
#include <android/log.h>
#include <EGL/egl.h>
#include <GLES3/gl3.h>
#include <cmath>
#include <cstring>
#include <vector>
#include <algorithm>
#include <ctime>
#include <cstdio>
#define PI 3.14159265f

// ---------- matematica ----------
struct V{float x=0,y=0,z=0;};
V operator+(V a,V b){return{a.x+b.x,a.y+b.y,a.z+b.z};}
V operator-(V a,V b){return{a.x-b.x,a.y-b.y,a.z-b.z};}
V operator*(V a,float k){return{a.x*k,a.y*k,a.z*k};}
float dot(V a,V b){return a.x*b.x+a.y*b.y+a.z*b.z;}
V cross(V a,V b){return{a.y*b.z-a.z*b.y,a.z*b.x-a.x*b.z,a.x*b.y-a.y*b.x};}
V norm(V a){return a*(1/sqrtf(dot(a,a)));}
V lerp(V a,V b,float t){return a+(b-a)*t;}
struct M{float m[16];};
M id(){M r={};r.m[0]=r.m[5]=r.m[10]=r.m[15]=1;return r;}
M mul(const M&a,const M&b){M r;for(int c=0;c<4;c++)for(int i=0;i<4;i++){float s=0;for(int k=0;k<4;k++)s+=a.m[k*4+i]*b.m[c*4+k];r.m[c*4+i]=s;}return r;}
M persp(float fy,float as,float n,float f){M r={};float t=1/tanf(fy/2);r.m[0]=t/as;r.m[5]=t;r.m[10]=(f+n)/(n-f);r.m[11]=-1;r.m[14]=2*f*n/(n-f);return r;}
M lookAt(V e,V c,V up){V f=norm(c-e),s=norm(cross(f,up)),u=cross(s,f);M r=id();
 r.m[0]=s.x;r.m[4]=s.y;r.m[8]=s.z;r.m[1]=u.x;r.m[5]=u.y;r.m[9]=u.z;r.m[2]=-f.x;r.m[6]=-f.y;r.m[10]=-f.z;
 r.m[12]=-dot(s,e);r.m[13]=-dot(u,e);r.m[14]=dot(f,e);return r;}
struct T{V p,r,s{1,1,1};};
M model(const T&t){
 float cx=cosf(t.r.x),sx=sinf(t.r.x),cy=cosf(t.r.y),sy=sinf(t.r.y),cz=cosf(t.r.z),sz=sinf(t.r.z);
 M a=id(),b=id(),c=id();
 a.m[5]=cx;a.m[6]=sx;a.m[9]=-sx;a.m[10]=cx;
 b.m[0]=cy;b.m[2]=-sy;b.m[8]=sy;b.m[10]=cy;
 c.m[0]=cz;c.m[1]=sz;c.m[4]=-sz;c.m[5]=cz;
 M r=mul(c,mul(b,a));
 for(int i=0;i<4;i++){r.m[i]*=t.s.x;r.m[4+i]*=t.s.y;r.m[8+i]*=t.s.z;}
 r.m[12]=t.p.x;r.m[13]=t.p.y;r.m[14]=t.p.z;return r;}

// ---------- cena + animacao ----------
struct Key{float t;T x;};
struct Obj{int mesh;V col;T cur;std::vector<Key> k;};
std::vector<Obj> objs;
int sel=-1,tool=3,W=1,H=1;      // tool: 0 mover,1 girar,2 escalar,3 camera
bool playing=false;float tm=0;const float DUR=5;
float yaw=.6f,pitch=.4f,cd=8;V tgt{0,.5f,0};const float FOV=1.047f;
V camEye(){return tgt+V{cosf(pitch)*sinf(yaw),sinf(pitch),cosf(pitch)*cosf(yaw)}*cd;}
T eval(Obj&o,float t){
 auto&k=o.k;if(k.empty())return o.cur;
 if(t<=k.front().t)return k.front().x;if(t>=k.back().t)return k.back().x;
 size_t i=0;while(k[i+1].t<t)i++;
 float u=(t-k[i].t)/(k[i+1].t-k[i].t);T r;
 r.p=lerp(k[i].x.p,k[i+1].x.p,u);r.r=lerp(k[i].x.r,k[i+1].x.r,u);r.s=lerp(k[i].x.s,k[i+1].x.s,u);return r;}
void applyAnim(){for(auto&o:objs)if(!o.k.empty())o.cur=eval(o,tm);}
void addObj(int mesh){
 static const V pal[]={{.9f,.35f,.3f},{.3f,.7f,.9f},{.5f,.85f,.4f},{.95f,.8f,.3f},{.7f,.45f,.9f}};
 Obj o;o.mesh=mesh;o.col=pal[objs.size()%5];
 o.cur.p={(objs.size()%4)*1.4f-2.1f,mesh==2?0.f:.5f,0};
 if(mesh==2)o.cur.s={2,2,2};
 objs.push_back(o);sel=(int)objs.size()-1;}

// ---------- GL ----------
const char*VS=R"(#version 300 es
layout(location=0) in vec3 aP; layout(location=1) in vec3 aN;
uniform mat4 uMVP; uniform mat4 uM; out vec3 vN;
void main(){gl_Position=uMVP*vec4(aP,1.0); vN=mat3(uM)*aN;})";
const char*FS=R"(#version 300 es
precision mediump float; in vec3 vN; uniform vec4 uC; uniform float uL; out vec4 o;
void main(){float d=1.0; if(uL>0.5){d=0.25+0.75*max(dot(normalize(vN),normalize(vec3(.4,.8,.5))),0.0);} o=vec4(uC.rgb*d,uC.a);})";
GLuint uMVP,uM,uC,uL;
struct Mesh{GLuint vao=0,vbo=0;int n=0;GLenum mode=GL_TRIANGLES;};
Mesh meshes[5]; // 0 cubo,1 esfera,2 plano,3 quad2D,4 grade
GLuint sh(GLenum t,const char*s){GLuint h=glCreateShader(t);glShaderSource(h,1,&s,0);glCompileShader(h);GLint ok;glGetShaderiv(h,GL_COMPILE_STATUS,&ok);
 if(!ok){char b[512];glGetShaderInfoLog(h,512,0,b);__android_log_print(ANDROID_LOG_ERROR,"NA","%s",b);}return h;}
void vtx(std::vector<float>&v,V p,V n){v.insert(v.end(),{p.x,p.y,p.z,n.x,n.y,n.z});}
Mesh upload(const std::vector<float>&v,GLenum mode){
 Mesh m;m.n=(int)v.size()/6;m.mode=mode;
 glGenVertexArrays(1,&m.vao);glGenBuffers(1,&m.vbo);glBindVertexArray(m.vao);glBindBuffer(GL_ARRAY_BUFFER,m.vbo);
 glBufferData(GL_ARRAY_BUFFER,v.size()*4,v.data(),GL_STATIC_DRAW);
 glEnableVertexAttribArray(0);glVertexAttribPointer(0,3,GL_FLOAT,GL_FALSE,24,(void*)0);
 glEnableVertexAttribArray(1);glVertexAttribPointer(1,3,GL_FLOAT,GL_FALSE,24,(void*)12);return m;}
void buildMeshes(){
 std::vector<float> a;
 V F[6][3]={{{1,0,0},{0,1,0},{0,0,1}},{{-1,0,0},{0,0,1},{0,1,0}},{{0,1,0},{0,0,1},{1,0,0}},
            {{0,-1,0},{1,0,0},{0,0,1}},{{0,0,1},{1,0,0},{0,1,0}},{{0,0,-1},{0,1,0},{1,0,0}}};
 int ix[6]={0,1,2,0,2,3};
 for(auto&f:F){V n=f[0],u=f[1],v=f[2],c=n*.5f;V p[4]={c-u*.5f-v*.5f,c+u*.5f-v*.5f,c+u*.5f+v*.5f,c-u*.5f+v*.5f};
  for(int i:ix)vtx(a,p[i],n);}
 meshes[0]=upload(a,GL_TRIANGLES);
 a.clear();
 auto sp=[](int i,int j){float th=i*PI/16,ph=j*2*PI/24;return V{sinf(th)*cosf(ph),cosf(th),sinf(th)*sinf(ph)};};
 for(int i=0;i<16;i++)for(int j=0;j<24;j++){V p=sp(i,j),q=sp(i+1,j),r=sp(i+1,j+1),s=sp(i,j+1);
  vtx(a,p*.5f,p);vtx(a,q*.5f,q);vtx(a,r*.5f,r);vtx(a,p*.5f,p);vtx(a,r*.5f,r);vtx(a,s*.5f,s);}
 meshes[1]=upload(a,GL_TRIANGLES);
 a.clear();V up{0,1,0};
 V pl[6]={{-1,0,-1},{-1,0,1},{1,0,1},{-1,0,-1},{1,0,1},{1,0,-1}};for(V p:pl)vtx(a,p,up);
 meshes[2]=upload(a,GL_TRIANGLES);
 a.clear();
 V qd[6]={{0,0,0},{1,0,0},{1,1,0},{0,0,0},{1,1,0},{0,1,0}};for(V p:qd)vtx(a,p,{0,0,1});
 meshes[3]=upload(a,GL_TRIANGLES);
 a.clear();
 for(int i=-10;i<=10;i++){vtx(a,{(float)i,0,-10},up);vtx(a,{(float)i,0,10},up);vtx(a,{-10,0,(float)i},up);vtx(a,{10,0,(float)i},up);}
 meshes[4]=upload(a,GL_LINES);}
void initGL(){
 GLuint p=glCreateProgram();glAttachShader(p,sh(GL_VERTEX_SHADER,VS));glAttachShader(p,sh(GL_FRAGMENT_SHADER,FS));
 glLinkProgram(p);glUseProgram(p);
 uMVP=glGetUniformLocation(p,"uMVP");uM=glGetUniformLocation(p,"uM");uC=glGetUniformLocation(p,"uC");uL=glGetUniformLocation(p,"uL");
 glEnable(GL_BLEND);glBlendFunc(GL_SRC_ALPHA,GL_ONE_MINUS_SRC_ALPHA);buildMeshes();}
void draw(Mesh&m,const M&mvp,const M&mod,float r,float g,float b,float a,float lit){
 glUniformMatrix4fv(uMVP,1,GL_FALSE,mvp.m);glUniformMatrix4fv(uM,1,GL_FALSE,mod.m);
 glUniform4f(uC,r,g,b,a);glUniform1f(uL,lit);glBindVertexArray(m.vao);glDrawArrays(m.mode,0,m.n);}

// ---------- UI 2D ----------
void rect(float x,float y,float w,float h,float r,float g,float b,float a=1){
 M m={};m.m[0]=2*w/W;m.m[5]=-2*h/H;m.m[10]=1;m.m[12]=2*x/W-1;m.m[13]=1-2*y/H;m.m[15]=1;
 draw(meshes[3],m,id(),r,g,b,a,0);}
const char*GN="ABCDEHIKLMNOPRSTUVYXZ0123456789";
const char*GG[]={"010101111101101","110101110101110","011100100100011","110101101101110","111100110100111",
 "101101111101101","111010010010111","101101110101101","100100100100111","101111111101101","110101101101101",
 "010101101101010","110101110100100","110101110101101","011100010001110","111010010010010","101101101101111",
 "101101101101010","101101010010010","101101010101101","111001010100111","111101101101111","010110010010111","111001111100111","111001111001111","101101111001001","111100111001111","111100111101111","111001001010010","111101111101111","111101111001111"};
void text(const char*s,float x,float y,float ps,float r,float g,float b){
 for(;*s;s++){const char*p=strchr(GN,*s);
  if(p){const char*gl=GG[p-GN];for(int k=0;k<15;k++)if(gl[k]=='1')rect(x+(k%3)*ps,y+(k/3)*ps,ps,ps,r,g,b);}
  x+=4*ps;}}
const char*BL[10]={"CUBE","SPH","PLN","MOVE","ROT","SCL","CAM","KEY","PLAY","DEL"};
float BC[10][3]={{.2f,.6f,.3f},{.2f,.6f,.3f},{.2f,.6f,.3f},{.2f,.4f,.8f},{.2f,.4f,.8f},{.2f,.4f,.8f},{.2f,.4f,.8f},{.9f,.75f,.1f},{.9f,.5f,.1f},{.8f,.2f,.2f}};
float ML(){return W*.05f;} float bw(){return (W-2*ML())/10.f;} float bh(){return H*.1f;} float tlh(){return H*.09f;} float tly(){return H-H*.045f-tlh();}
float tx(float t){return ML()+t/DUR*(W-2*ML());}

// ---------- EGL ----------
EGLDisplay dpy=EGL_NO_DISPLAY;EGLSurface surf=EGL_NO_SURFACE;EGLContext ctx=EGL_NO_CONTEXT;bool ready=false;
bool initEGL(ANativeWindow*w){
 dpy=eglGetDisplay(EGL_DEFAULT_DISPLAY);eglInitialize(dpy,0,0);
 const EGLint ca[]={EGL_RENDERABLE_TYPE,0x0040,EGL_SURFACE_TYPE,EGL_WINDOW_BIT,EGL_RED_SIZE,8,EGL_GREEN_SIZE,8,EGL_BLUE_SIZE,8,EGL_DEPTH_SIZE,24,EGL_NONE};
 EGLConfig cfg;EGLint n=0;eglChooseConfig(dpy,ca,&cfg,1,&n);if(!n)return false;
 EGLint fmt;eglGetConfigAttrib(dpy,cfg,EGL_NATIVE_VISUAL_ID,&fmt);ANativeWindow_setBuffersGeometry(w,0,0,fmt);
 surf=eglCreateWindowSurface(dpy,cfg,w,0);
 const EGLint xa[]={EGL_CONTEXT_CLIENT_VERSION,3,EGL_NONE};ctx=eglCreateContext(dpy,cfg,0,xa);
 if(!eglMakeCurrent(dpy,surf,surf,ctx))return false;
 eglQuerySurface(dpy,surf,EGL_WIDTH,&W);eglQuerySurface(dpy,surf,EGL_HEIGHT,&H);return true;}
void termEGL(){
 if(dpy!=EGL_NO_DISPLAY){eglMakeCurrent(dpy,EGL_NO_SURFACE,EGL_NO_SURFACE,EGL_NO_CONTEXT);
  if(ctx!=EGL_NO_CONTEXT)eglDestroyContext(dpy,ctx);if(surf!=EGL_NO_SURFACE)eglDestroySurface(dpy,surf);eglTerminate(dpy);}
 dpy=EGL_NO_DISPLAY;ctx=EGL_NO_CONTEXT;surf=EGL_NO_SURFACE;}

// ---------- render ----------
M gVP;int gAxis=-1,gIdx=0;bool gDrag=false;
const V AX[3]={{1,0,0},{0,1,0},{0,0,1}};
const float AC[3][3]={{.9f,.25f,.25f},{.4f,.8f,.3f},{.3f,.5f,1.f}};
float gl(){return cd*.2f;}
bool prj(V p,float&x,float&y){const float*m=gVP.m;
 float cx=m[0]*p.x+m[4]*p.y+m[8]*p.z+m[12],cy=m[1]*p.x+m[5]*p.y+m[9]*p.z+m[13],cw=m[3]*p.x+m[7]*p.y+m[11]*p.z+m[15];
 if(cw<.01f)return false;x=(cx/cw*.5f+.5f)*W;y=(1-(cy/cw*.5f+.5f))*H;return true;}
V ringPt(int a,int i){float th=i*2*PI/32,c=cosf(th)*gl()*.8f,s=sinf(th)*gl()*.8f;V o=objs[sel].cur.p;
 return a==0?o+V{0,c,s}:a==1?o+V{s,0,c}:o+V{c,s,0};}
int hitGizmo(float x,float y){
 if(sel<0||tool>2)return -1;
 V o=objs[sel].cur.p;float ox,oy;if(!prj(o,ox,oy))return -1;
 int best=-1;float bd=48;
 for(int a=0;a<3;a++){float d=1e9f;int bi=0;
  if(tool==1){for(int i=0;i<32;i++){float px,py;if(prj(ringPt(a,i),px,py)){float dd=hypotf(px-x,py-y);if(dd<d){d=dd;bi=i;}}}}
  else{float ex,ey;if(prj(o+AX[a]*gl(),ex,ey)){float vx=ex-ox,vy=ey-oy,t=std::clamp(((x-ox)*vx+(y-oy)*vy)/(vx*vx+vy*vy+1e-3f),0.f,1.f);d=hypotf(x-ox-vx*t,y-oy-vy*t);}}
  if(d<bd){bd=d;best=a;gIdx=bi;}}
 return best;}
void drawGizmo(){
 V p=objs[sel].cur.p;float L=gl(),th=L*.025f;
 auto box=[&](V c,V sc,const float*k){T t;t.p=c;t.s=sc;M m=model(t);draw(meshes[0],mul(gVP,m),m,k[0],k[1],k[2],1,0);};
 static const float Y[3]={1,.9f,.2f};
 for(int a=0;a<3;a++){const float*k=(gDrag&&a==gAxis)?Y:AC[a];
  if(tool==1){for(int i=0;i<32;i++)box(ringPt(a,i),V{th*2,th*2,th*2},k);}
  else{V sc{th,th,th};(&sc.x)[a]=L;box(p+AX[a]*(L*.5f),sc,k);float e=th*(tool==2?7.f:4.f);box(p+AX[a]*L,V{e,e,e},k);}}}
struct ND{float x,y,z;int a;bool pos;};
float navR(){return H*.11f;} float navX(){return W-ML()-navR()-8;} float navY(){return bh()+navR()+16;}
void navPts(ND*d){V f=norm(tgt-camEye()),s=norm(cross(f,V{0,1,0})),u=cross(s,f);float R=navR();
 for(int i=0;i<6;i++){int a=i%3;V v=AX[a]*(i<3?1.f:-1.f);d[i]={navX()+dot(v,s)*R*.72f,navY()-dot(v,u)*R*.72f,dot(v,f),a,i<3};}}
void drawNav(){ND d[6];navPts(d);float R=navR(),cx=navX(),cy=navY();
 rect(cx-R-6,cy-R-6,2*R+12,2*R+12,0,0,0,.28f);
 std::sort(d,d+6,[](const ND&p,const ND&q){return p.z>q.z;});
 static const char*LB[3]={"X","Y","Z"};
 for(auto&e:d){const float*c=AC[e.a];float k=e.pos?1.f:.5f,r=e.pos?H*.024f:H*.017f;
  if(e.pos)for(int j=1;j<6;j++)rect(cx+(e.x-cx)*j/6-2,cy+(e.y-cy)*j/6-2,4,4,c[0],c[1],c[2]);
  rect(e.x-r,e.y-r,2*r,2*r,c[0]*k,c[1]*k,c[2]*k);
  if(e.pos){float ps=H*.007f;text(LB[e.a],e.x-1.5f*ps,e.y-2.5f*ps,ps,1,1,1);}}}
void frame(){
 glViewport(0,0,W,H);glClearColor(.18f,.19f,.22f,1);glClear(GL_COLOR_BUFFER_BIT|GL_DEPTH_BUFFER_BIT);
 glEnable(GL_DEPTH_TEST);
 gVP=mul(persp(FOV,(float)W/H,.1f,100),lookAt(camEye(),tgt,{0,1,0}));
 draw(meshes[4],gVP,id(),.4f,.4f,.45f,1,0);
 for(int i=0;i<(int)objs.size();i++){Obj&o=objs[i];M mod=model(o.cur);float h=(i==sel)?.35f:0;
  draw(meshes[o.mesh],mul(gVP,mod),mod,o.col.x+(1-o.col.x)*h,o.col.y+(1-o.col.y)*h,o.col.z+(1-o.col.z)*h,1,1);}
 glDisable(GL_DEPTH_TEST);
 if(sel>=0&&tool<3)drawGizmo();
 float ps=bh()/8;
 for(int i=0;i<10;i++){bool on=(i>=3&&i<=6&&tool==i-3)||(i==8&&playing);float k=on?1.f:.55f,x=ML()+i*bw();
  rect(x+3,4,bw()-6,bh()-8,BC[i][0]*k,BC[i][1]*k,BC[i][2]*k);
  float tw=strlen(BL[i])*4*ps-ps;text(BL[i],x+(bw()-tw)/2,(bh()-5*ps)/2,ps,1,1,1);}
 float y0=tly(),h=tlh(),x0=ML(),w=W-2*x0,p2=h/16;
 rect(x0,y0,w,h,.12f,.12f,.14f);
 for(int f=0;f<=(int)(DUR*24);f+=6){float x=tx(f/24.f);bool big=f%24==0;
  rect(x-1,y0+h*(big?.5f:.6f),2,h*(big?.2f:.1f),.5f,.5f,.55f);
  if(big){char b[8];snprintf(b,8,"%d",f);text(b,x+4,y0+h*.12f,p2*.8f,.7f,.7f,.75f);}}
 if(sel>=0)for(auto&k:objs[sel].k)rect(tx(k.t)-h*.09f,y0+h*.76f,h*.18f,h*.18f,.95f,.8f,.1f);
 rect(tx(tm)-2,y0,4,h,1,.3f,.3f);
 char b[16];snprintf(b,16,"%d",(int)roundf(tm*24));float fp=H*.008f;text(b,x0+w-strlen(b)*4*fp-8,y0-6*fp-6,fp,1,1,1);
 drawNav();
 eglSwapBuffers(dpy,surf);}

// ---------- input ----------
void press(int i){
 if(i<0||i>9)return;
 if(i<3)addObj(i);else if(i<7)tool=i-3;
 else if(i==7&&sel>=0){Obj&o=objs[sel];bool f=false;
  for(auto&k:o.k)if(fabsf(k.t-tm)<.05f){k.x=o.cur;f=true;}
  if(!f){o.k.push_back({tm,o.cur});std::sort(o.k.begin(),o.k.end(),[](const Key&a,const Key&b){return a.t<b.t;});}}
 else if(i==8)playing=!playing;
 else if(i==9&&sel>=0){objs.erase(objs.begin()+sel);sel=-1;}}
void scrub(float x){tm=roundf(std::clamp((x-ML())/(W-2*ML()),0.f,1.f)*DUR*24)/24;applyAnim();}
void pick(float x,float y){
 V e=camEye(),f=norm(tgt-e),s=norm(cross(f,V{0,1,0})),u=cross(s,f);
 float th=tanf(FOV/2),as=(float)W/H;V d=norm(f+s*((2*x/W-1)*th*as)+u*((1-2*y/H)*th));
 static const float RF[3]={.87f,.5f,1.42f};int best=-1;float bt=1e9f;
 for(int i=0;i<(int)objs.size();i++){T&t=objs[i].cur;float r=RF[objs[i].mesh]*std::max({t.s.x,t.s.y,t.s.z});
  V oc=e-t.p;float b=dot(oc,d),c=dot(oc,oc)-r*r,ds=b*b-c;if(ds<0)continue;
  float tt=-b-sqrtf(ds);if(tt>0&&tt<bt){bt=tt;best=i;}}
 sel=best;}
void orbit(float dx,float dy){yaw-=dx*.006f;pitch=std::clamp(pitch+dy*.006f,-1.5f,1.5f);}
void gdrag(float dx,float dy){
 T&t=objs[sel].cur;V o=t.p;float ox,oy,ex,ey;
 if(tool==1){float px,py,qx,qy;if(!prj(ringPt(gAxis,gIdx+1),px,py)||!prj(ringPt(gAxis,gIdx+31),qx,qy))return;
  float vx=px-qx,vy=py-qy,l=hypotf(vx,vy);if(l<1)return;(&t.r.x)[gAxis]+=(dx*vx+dy*vy)/l*.012f;return;}
 if(!prj(o,ox,oy)||!prj(o+AX[gAxis]*gl(),ex,ey))return;
 float vx=ex-ox,vy=ey-oy,k=(dx*vx+dy*vy)/(vx*vx+vy*vy+1e-3f);
 if(tool==0)t.p=t.p+AX[gAxis]*(k*gl());else{float&sc=(&t.s.x)[gAxis];sc=std::max(.05f,sc*(1+k));}}
void snap(float x,float y){ND d[6];navPts(d);
 for(auto&e:d)if(hypotf(x-e.x,y-e.y)<H*.035f){
  if(e.a==0){yaw=e.pos?PI/2:-PI/2;pitch=0;}else if(e.a==1)pitch=e.pos?1.45f:-1.45f;else{yaw=e.pos?0.f:PI;pitch=0;}return;}}
int32_t onInput(android_app*,AInputEvent*e){
 static int mode=0;static float lx,ly,sx,sy,pinch;static bool moved,rl;
 if(AInputEvent_getType(e)!=AINPUT_EVENT_TYPE_MOTION)return 0;
 int act=AMotionEvent_getAction(e)&AMOTION_EVENT_ACTION_MASK,n=(int)AMotionEvent_getPointerCount(e);
 float x=AMotionEvent_getX(e,0),y=AMotionEvent_getY(e,0);
 if(act==AMOTION_EVENT_ACTION_DOWN){
  moved=false;rl=true;sx=x;sy=y;pinch=0;gDrag=false;
  if(y<bh()+8){press((int)floorf((x-ML())/bw()));mode=2;}
  else if(y>tly()){mode=3;scrub(x);}
  else if(hypotf(x-navX(),y-navY())<navR()+12)mode=4;
  else{int a=hitGizmo(x,y);if(a>=0){gAxis=a;gDrag=true;mode=5;}else mode=1;}
 }else if(act==AMOTION_EVENT_ACTION_POINTER_DOWN){moved=true;rl=true;pinch=0;}
 else if(act==AMOTION_EVENT_ACTION_POINTER_UP){rl=true;pinch=0;}
 else if(act==AMOTION_EVENT_ACTION_MOVE){
  if(mode==3)scrub(x);
  else if(mode==1&&n>=2){float d=hypotf(AMotionEvent_getX(e,1)-x,AMotionEvent_getY(e,1)-y);
   if(pinch>0&&d>1)cd=std::clamp(cd*pinch/d,2.f,40.f);pinch=d;moved=true;}
  else if(mode==1||mode==4||mode==5){
   if(rl){rl=false;lx=x;ly=y;}
   else{float dx=x-lx,dy=y-ly;lx=x;ly=y;if(hypotf(x-sx,y-sy)>20)moved=true;
    if(mode==5)gdrag(dx,dy);else if(moved)orbit(dx,dy);}}
 }else if(act==AMOTION_EVENT_ACTION_UP||act==AMOTION_EVENT_ACTION_CANCEL){
  if(mode==1&&!moved)pick(x,y);if(mode==4&&!moved)snap(x,y);mode=0;gDrag=false;}
 return 1;}
void onCmd(android_app*a,int32_t c){
 if(c==APP_CMD_INIT_WINDOW&&a->window){if(initEGL(a->window)){initGL();ready=true;}}
 else if(c==APP_CMD_TERM_WINDOW){ready=false;termEGL();}}

void android_main(android_app*app){
 app->onAppCmd=onCmd;app->onInputEvent=onInput;
 auto now=[](){timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;};
 double last=now();
 while(true){
  int ev;android_poll_source*src;
  while(ALooper_pollOnce(ready?0:-1,nullptr,&ev,(void**)&src)>=0){
   if(src)src->process(app,src);
   if(app->destroyRequested){termEGL();return;}}
  if(ready){double t=now();float dt=(float)(t-last);last=t;
   if(playing){tm+=dt;if(tm>DUR)tm=0;applyAnim();}
   frame();}else last=now();}}
