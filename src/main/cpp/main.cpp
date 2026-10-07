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
#include <cstdarg>
#include <cstdint>
#include <string>
#include <dirent.h>
#define STB_TRUETYPE_IMPLEMENTATION
#include "stb_truetype.h"
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
struct Obj{int mesh;V col;T cur;std::vector<Key> k;char nm[24]="";int parent=-1;float len=1;};
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
M worldM(int i,int d=0){M l=model(objs[i].cur);int p=objs[i].parent;return(p>=0&&d<32)?mul(worldM(p,d+1),l):l;}
V wp(int i){M m=worldM(i);return V{m.m[12],m.m[13],m.m[14]};}
V invPt(const M&m,V p){V c0{m.m[0],m.m[1],m.m[2]},c1{m.m[4],m.m[5],m.m[6]},c2{m.m[8],m.m[9],m.m[10]},d=p-V{m.m[12],m.m[13],m.m[14]};
 float det=dot(c0,cross(c1,c2));if(fabsf(det)<1e-8f)return d;return V{dot(cross(c1,c2),d),dot(cross(c2,c0),d),dot(cross(c0,c1),d)}*(1/det);}
void addObj(int mesh){
 static const V pal[]={{.9f,.35f,.3f},{.3f,.7f,.9f},{.5f,.85f,.4f},{.95f,.8f,.3f},{.7f,.45f,.9f}};
 Obj o;o.mesh=mesh;o.col=pal[objs.size()%5];static int cnt[6]={0,0,0,0,0,0};static const char*NM[6]={"Cube","Sphere","Plane","","","Bone"};snprintf(o.nm,24,"%s.%03d",NM[mesh],++cnt[mesh]);
 if(mesh==5){o.col={.85f,.85f,.65f};o.cur.p={0,0,0};if(sel>=0&&objs[sel].mesh==5){o.parent=sel;o.cur.p={0,objs[sel].len,0};}}
 else{o.cur.p={(objs.size()%4)*1.4f-2.1f,mesh==2?0.f:.5f,0};if(mesh==2)o.cur.s={2,2,2};}
 objs.push_back(o);sel=(int)objs.size()-1;}
void clearParent(int c){V w=wp(c);objs[c].parent=-1;objs[c].cur.p=w;}
void delObj(int i){for(int j=0;j<(int)objs.size();j++)if(objs[j].parent==i)clearParent(j);
 objs.erase(objs.begin()+i);for(auto&o:objs)if(o.parent>i)o.parent--;sel=-1;}

// ---------- GL ----------
const char*VS=R"(#version 300 es
layout(location=0) in vec3 aP; layout(location=1) in vec3 aN;
uniform mat4 uMVP; uniform mat4 uM; out vec3 vN; out vec3 vP;
void main(){gl_Position=uMVP*vec4(aP,1.0); vN=mat3(uM)*aN; vP=aP;})";
const char*FS=R"(#version 300 es
precision highp float; in vec3 vN; in vec3 vP; uniform vec4 uC; uniform float uL; uniform vec3 uS; out vec4 o;
void main(){if(uL<-1.5){vec2 q=(vP.xy-.5)*uS.xy;float dd=(abs(q.x)+abs(q.y)-uS.x*.5)*.7071;o=vec4(uC.rgb,uC.a*clamp(.5-dd,0.0,1.0));return;} if(uL<0.0){vec2 q=(vP.xy-.5)*uS.xy;vec2 e=abs(q)-uS.xy*.5+uS.z;float dd=length(max(e,0.0))+min(max(e.x,e.y),0.0)-uS.z;o=vec4(uC.rgb,uC.a*clamp(.5-dd,0.0,1.0));return;} float d=1.0; if(uL>0.5){d=0.25+0.75*max(dot(normalize(vN),normalize(vec3(.4,.8,.5))),0.0);} o=vec4(uC.rgb*d,uC.a);})";
GLuint uMVP,uM,uC,uL,uS,gProg=0;float gS[3]={1,1,0};void initText();
struct Mesh{GLuint vao=0,vbo=0;int n=0;GLenum mode=GL_TRIANGLES;std::vector<float> cpu;};
Mesh meshes[6]; // 0 cubo,1 esfera,2 plano,3 quad2D,4 grade,5 osso
GLuint sh(GLenum t,const char*s){GLuint h=glCreateShader(t);glShaderSource(h,1,&s,0);glCompileShader(h);GLint ok;glGetShaderiv(h,GL_COMPILE_STATUS,&ok);
 if(!ok){char b[512];glGetShaderInfoLog(h,512,0,b);__android_log_print(ANDROID_LOG_ERROR,"NA","%s",b);}return h;}
void vtx(std::vector<float>&v,V p,V n){v.insert(v.end(),{p.x,p.y,p.z,n.x,n.y,n.z});}
Mesh upload(const std::vector<float>&v,GLenum mode){
 Mesh m;m.n=(int)v.size()/6;m.mode=mode;m.cpu=v;
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
 meshes[4]=upload(a,GL_LINES);
 a.clear();{V h{0,0,0},t{0,1,0};float w=.12f,y=.15f;V r[4]={{w,y,0},{0,y,w},{-w,y,0},{0,y,-w}};
  for(int i=0;i<4;i++){V p=r[i],q=r[(i+1)%4];V n1=norm(cross(p-h,q-h)),n2=norm(cross(q-t,p-t));
   vtx(a,h,n1);vtx(a,p,n1);vtx(a,q,n1);vtx(a,t,n2);vtx(a,q,n2);vtx(a,p,n2);}}
 meshes[5]=upload(a,GL_TRIANGLES);}
void initGL(){
 GLuint p=gProg=glCreateProgram();glAttachShader(p,sh(GL_VERTEX_SHADER,VS));glAttachShader(p,sh(GL_FRAGMENT_SHADER,FS));
 glLinkProgram(p);glUseProgram(p);
 uMVP=glGetUniformLocation(p,"uMVP");uM=glGetUniformLocation(p,"uM");uC=glGetUniformLocation(p,"uC");uL=glGetUniformLocation(p,"uL");uS=glGetUniformLocation(p,"uS");
 glEnable(GL_BLEND);glBlendFunc(GL_SRC_ALPHA,GL_ONE_MINUS_SRC_ALPHA);buildMeshes();initText();}
void draw(Mesh&m,const M&mvp,const M&mod,float r,float g,float b,float a,float lit){
 glUniformMatrix4fv(uMVP,1,GL_FALSE,mvp.m);glUniformMatrix4fv(uM,1,GL_FALSE,mod.m);
 glUniform4f(uC,r,g,b,a);glUniform1f(uL,lit);glUniform3f(uS,gS[0],gS[1],gS[2]);glBindVertexArray(m.vao);glDrawArrays(m.mode,0,m.n);}

// ---------- UI 2D ----------
void rect(float x,float y,float w,float h,float r,float g,float b,float a=1,float rad=0){
 M m={};m.m[0]=2*w/W;m.m[5]=-2*h/H;m.m[10]=1;m.m[12]=2*x/W-1;m.m[13]=1-2*y/H;m.m[15]=1;
 gS[0]=w;gS[1]=h;gS[2]=std::min(rad,std::min(w,h)/2);draw(meshes[3],m,id(),r,g,b,a,-1);}
const char*GN="ABCDEHIKLMNOPRSTUVYXZ0123456789";
const char*GG[]={"010101111101101","110101110101110","011100100100011","110101101101110","111100110100111",
 "101101111101101","111010010010111","101101110101101","100100100100111","101111111101101","110101101101101",
 "010101101101010","110101110100100","110101110101101","011100010001110","111010010010010","101101101101111",
 "101101101101010","101101010010010","101101010101101","111001010100111","111101101101111","010110010010111","111001111100111","111001111001111","101101111001001","111100111001111","111100111101111","111001001010010","111101111101111","111101111001111"};
void btext(const char*s,float x,float y,float ps,float r,float g,float b){
 for(;*s;s++){const char*p=strchr(GN,*s);
  if(p){const char*gl=GG[p-GN];for(int k=0;k<15;k++)if(gl[k]=='1')rect(x+(k%3)*ps,y+(k/3)*ps,ps,ps,r,g,b);}
  x+=4*ps;}}
// ---- fonte TTF do sistema (stb_truetype) ----
std::vector<unsigned char> gAtlas;stbtt_bakedchar gBC[96];GLuint gTex=0,gTP=0,gTVao=0,gTVbo=0,uTS,uTC;
const float FPX=44;
bool loadFont(){
 FILE*f=nullptr;
 static const char*P[]={"/system/fonts/Roboto-Regular.ttf","/system/fonts/RobotoStatic-Regular.ttf","/system/fonts/Roboto[wdth,wght].ttf","/system/fonts/NotoSans-Regular.ttf","/system/fonts/DroidSans.ttf"};
 for(auto q:P){f=fopen(q,"rb");if(f)break;}
 for(int pass=0;pass<2&&!f;pass++){if(DIR*dr=opendir("/system/fonts")){while(dirent*en=readdir(dr)){std::string n=en->d_name;
  bool ttf=n.size()>8&&n.compare(n.size()-4,4,".ttf")==0,bad=false;
  for(const char*w:{"Italic","Bold","Light","Thin","Medium","Black","Mono","Slab","Serif","Emoji","Symbols","Cjk","CJK","Condensed"})if(n.find(w)!=std::string::npos)bad=true;
  bool ok=pass==0?n.find("Roboto")!=std::string::npos:n.find("Regular")!=std::string::npos;
  if(ttf&&ok&&!bad){f=fopen(("/system/fonts/"+n).c_str(),"rb");if(f)break;}}closedir(dr);}}
 if(!f)return false;
 fseek(f,0,SEEK_END);long sz=ftell(f);fseek(f,0,SEEK_SET);std::vector<unsigned char> d(sz>0?sz:1);
 size_t rd=fread(d.data(),1,sz,f);fclose(f);if(sz<=0||(long)rd!=sz)return false;
 gAtlas.assign(512*512,0);
 if(stbtt_BakeFontBitmap(d.data(),0,FPX,gAtlas.data(),512,512,32,96,gBC)<=0){gAtlas.clear();return false;}
 return true;}
void initText(){
 static bool tried=false;if(!tried){tried=true;loadFont();}
 gTex=0;if(gAtlas.empty())return;
 const char*vs="#version 300 es\nlayout(location=0) in vec4 aV; uniform vec2 uScr; out vec2 vT;\nvoid main(){gl_Position=vec4(aV.x/uScr.x*2.0-1.0,1.0-aV.y/uScr.y*2.0,0.0,1.0); vT=aV.zw;}";
 const char*fs="#version 300 es\nprecision mediump float; in vec2 vT; uniform sampler2D uTex; uniform vec4 uC; out vec4 o;\nvoid main(){o=vec4(uC.rgb,uC.a*texture(uTex,vT).r);}";
 GLuint p=glCreateProgram();glAttachShader(p,sh(GL_VERTEX_SHADER,vs));glAttachShader(p,sh(GL_FRAGMENT_SHADER,fs));glLinkProgram(p);gTP=p;
 uTS=glGetUniformLocation(p,"uScr");uTC=glGetUniformLocation(p,"uC");glUseProgram(p);glUniform1i(glGetUniformLocation(p,"uTex"),0);glUseProgram(gProg);
 glGenTextures(1,&gTex);glBindTexture(GL_TEXTURE_2D,gTex);glPixelStorei(GL_UNPACK_ALIGNMENT,1);
 glTexImage2D(GL_TEXTURE_2D,0,GL_R8,512,512,0,GL_RED,GL_UNSIGNED_BYTE,gAtlas.data());
 glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MIN_FILTER,GL_LINEAR);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MAG_FILTER,GL_LINEAR);
 glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_WRAP_S,GL_CLAMP_TO_EDGE);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_WRAP_T,GL_CLAMP_TO_EDGE);
 glGenVertexArrays(1,&gTVao);glGenBuffers(1,&gTVbo);glBindVertexArray(gTVao);glBindBuffer(GL_ARRAY_BUFFER,gTVbo);
 glEnableVertexAttribArray(0);glVertexAttribPointer(0,4,GL_FLOAT,GL_FALSE,16,(void*)0);}
float tw(const char*s,float ps){if(!gTex)return strlen(s)*4*ps-ps;float w=0;for(;*s;s++){int c=(unsigned char)*s;if(c>=32&&c<128)w+=gBC[c-32].xadvance;}return w*ps*7/FPX;}
void text(const char*s,float x,float y,float ps,float r,float g,float b){
 if(!gTex){btext(s,x,y,ps,r,g,b);return;}
 float sc=ps*7/FPX,by=y+5*ps;std::vector<float> v;
 for(;*s;s++){int c=(unsigned char)*s;if(c<32||c>=128)continue;stbtt_aligned_quad q;float xp=0,yp=0;stbtt_GetBakedQuad(gBC,512,512,c-32,&xp,&yp,&q,1);
  float x0=x+q.x0*sc,x1=x+q.x1*sc,y0=by+q.y0*sc,y1=by+q.y1*sc;
  v.insert(v.end(),{x0,y0,q.s0,q.t0,x1,y0,q.s1,q.t0,x1,y1,q.s1,q.t1,x0,y0,q.s0,q.t0,x1,y1,q.s1,q.t1,x0,y1,q.s0,q.t1});x+=xp*sc;}
 if(v.empty())return;
 glUseProgram(gTP);glUniform2f(uTS,(float)W,(float)H);glUniform4f(uTC,r,g,b,1);glActiveTexture(GL_TEXTURE0);glBindTexture(GL_TEXTURE_2D,gTex);
 glBindVertexArray(gTVao);glBindBuffer(GL_ARRAY_BUFFER,gTVbo);glBufferData(GL_ARRAY_BUFFER,v.size()*4,v.data(),GL_STREAM_DRAW);
 glDrawArrays(GL_TRIANGLES,0,(int)v.size()/4);glUseProgram(gProg);}
struct Rc{float x,y,w,h;};struct Btn{Rc r;int id;};
std::vector<Btn> gBtn;std::vector<Rc> gBlock;Rc gTrack={0,0,0,0};
float U(){return H*.01f;}
bool inR(const Rc&r,float x,float y){return x>=r.x&&x<=r.x+r.w&&y>=r.y&&y<=r.y+r.h;}
void dia(float cx,float cy,float sz,float r,float g,float b){M m={};m.m[0]=2*sz/W;m.m[5]=-2*sz/H;m.m[10]=1;m.m[12]=2*(cx-sz/2)/W-1;m.m[13]=1-2*(cy-sz/2)/H;m.m[15]=1;
 gS[0]=sz;gS[1]=sz;gS[2]=0;draw(meshes[3],m,id(),r,g,b,1,-2);}
void tcen(const char*s,float cx,float cy,float ps,float r,float g,float b){text(s,cx-tw(s,ps)/2,cy-2.5f*ps,ps,r,g,b);}
void panel(float x,float y,float w,float h,float rad){rect(x,y,w,h,.13f,.13f,.14f,.9f,rad);gBlock.push_back({x,y,w,h});}
void pill(float x,float y,float w,float h,int bid,const char*lb,bool on,float cr,float cg,float cb){
 if(on){cr=.28f;cg=.45f;cb=.70f;}
 rect(x,y,w,h,cr,cg,cb,1,h*.28f);tcen(lb,x+w/2,y+h/2,h*.072f,.94f,.94f,.94f);gBtn.push_back({{x,y,w,h},bid});}
void icon(int bid,float cx,float cy,float s,bool on){
 float br=on?.28f:.33f,bg=on?.45f:.33f,bb=on?.70f:.35f;
 if(bid==6){rect(cx-s,cy-s,2*s,2*s,.92f,.92f,.92f,1,s);rect(cx-s*.7f,cy-s*.7f,1.4f*s,1.4f*s,br,bg,bb,1,s*.7f);rect(cx-s*.22f,cy-s*.22f,s*.44f,s*.44f,.92f,.92f,.92f,1,s*.22f);}
 else if(bid==3){rect(cx-s,cy-s*.09f,2*s,s*.18f,.92f,.92f,.92f);rect(cx-s*.09f,cy-s,s*.18f,2*s,.92f,.92f,.92f);
  dia(cx-s,cy,s*.7f,.92f,.92f,.92f);dia(cx+s,cy,s*.7f,.92f,.92f,.92f);dia(cx,cy-s,s*.7f,.92f,.92f,.92f);dia(cx,cy+s,s*.7f,.92f,.92f,.92f);}
 else if(bid==4){rect(cx-s,cy-s,2*s,2*s,.92f,.92f,.92f,1,s);rect(cx-s*.66f,cy-s*.66f,1.32f*s,1.32f*s,br,bg,bb,1,s*.66f);rect(cx+s*.42f,cy-s*.9f,s*.45f,s*.45f,1,.8f,.2f,1,s*.22f);}
 else{rect(cx-s,cy-s,2*s,2*s,.92f,.92f,.92f,1,s*.18f);rect(cx-s*.78f,cy-s*.78f,1.56f*s,1.56f*s,br,bg,bb,1,s*.1f);rect(cx-s*.55f,cy-s*.55f,s*.7f,s*.7f,.92f,.92f,.92f,1,s*.08f);}}
const char*BL[10]={"CUBE","SPH","PLN","MOVE","ROT","SCL","CAM","KEY","PLAY","DEL"};
float BC[10][3]={{.2f,.6f,.3f},{.2f,.6f,.3f},{.2f,.6f,.3f},{.2f,.4f,.8f},{.2f,.4f,.8f},{.2f,.4f,.8f},{.2f,.4f,.8f},{.9f,.75f,.1f},{.9f,.5f,.1f},{.8f,.2f,.2f}};
float ML(){return W*.04f;} float bw(){return (W-2*ML())/10.f;} float bh(){return H*.1f;} float tlh(){return H*.09f;} float tly(){return H-H*.045f-tlh();}
float tx(float t){return ML()+t/DUR*(W-2*ML());}

// ---------- EGL ----------
EGLDisplay dpy=EGL_NO_DISPLAY;EGLSurface surf=EGL_NO_SURFACE;EGLContext ctx=EGL_NO_CONTEXT;bool ready=false;
bool initEGL(ANativeWindow*w){
 dpy=eglGetDisplay(EGL_DEFAULT_DISPLAY);eglInitialize(dpy,0,0);
 EGLint ca[]={EGL_RENDERABLE_TYPE,0x0040,EGL_SURFACE_TYPE,EGL_WINDOW_BIT,EGL_RED_SIZE,8,EGL_GREEN_SIZE,8,EGL_BLUE_SIZE,8,EGL_DEPTH_SIZE,24,EGL_SAMPLE_BUFFERS,1,EGL_SAMPLES,4,EGL_NONE};
 EGLConfig cfg;EGLint n=0;eglChooseConfig(dpy,ca,&cfg,1,&n);if(!n){ca[12]=EGL_NONE;eglChooseConfig(dpy,ca,&cfg,1,&n);}if(!n)return false;
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
V ringPt(int a,int i){float th=i*2*PI/32,c=cosf(th)*gl()*.8f,s=sinf(th)*gl()*.8f;V o=wp(sel);
 return a==0?o+V{0,c,s}:a==1?o+V{s,0,c}:o+V{c,s,0};}
int hitGizmo(float x,float y){
 if(sel<0||tool>2)return -1;
 V o=wp(sel);float ox,oy;if(!prj(o,ox,oy))return -1;
 int best=-1;float bd=48;
 for(int a=0;a<3;a++){float d=1e9f;int bi=0;
  if(tool==1){for(int i=0;i<32;i++){float px,py;if(prj(ringPt(a,i),px,py)){float dd=hypotf(px-x,py-y);if(dd<d){d=dd;bi=i;}}}}
  else{float ex,ey;if(prj(o+AX[a]*gl(),ex,ey)){float vx=ex-ox,vy=ey-oy,t=std::clamp(((x-ox)*vx+(y-oy)*vy)/(vx*vx+vy*vy+1e-3f),0.f,1.f);d=hypotf(x-ox-vx*t,y-oy-vy*t);}}
  if(d<bd){bd=d;best=a;gIdx=bi;}}
 return best;}
void drawGizmo(){
 V p=wp(sel);float L=gl(),th=L*.025f;
 auto box=[&](V c,V sc,const float*k,int ms=0){T t;t.p=c;t.s=sc;M m=model(t);draw(meshes[ms],mul(gVP,m),m,k[0],k[1],k[2],1,0);};
 static const float Y[3]={1,.9f,.2f};
 for(int a=0;a<3;a++){const float*k=(gDrag&&a==gAxis)?Y:AC[a];
  if(tool==1){for(int i=0;i<32;i++)box(ringPt(a,i),V{th*3,th*3,th*3},k,1);}
  else{V sc{th,th,th};(&sc.x)[a]=L;box(p+AX[a]*(L*.5f),sc,k);float e=th*(tool==2?7.f:4.f);box(p+AX[a]*L,V{e,e,e},k,1);}}}
struct ND{float x,y,z;int a;bool pos;};
float navR(){return H*.1f;} float navX(){return W-ML()-navR()-H*.01f;} float navY(){return H*.072f+navR()+H*.02f;}
void navPts(ND*d){V f=norm(tgt-camEye()),s=norm(cross(f,V{0,1,0})),u=cross(s,f);float R=navR();
 for(int i=0;i<6;i++){int a=i%3;V v=AX[a]*(i<3?1.f:-1.f);d[i]={navX()+dot(v,s)*R*.72f,navY()-dot(v,u)*R*.72f,dot(v,f),a,i<3};}}
void drawNav(){ND d[6];navPts(d);float R=navR(),cx=navX(),cy=navY();
 rect(cx-R-6,cy-R-6,2*R+12,2*R+12,0,0,0,.3f,R+6);
 std::sort(d,d+6,[](const ND&p,const ND&q){return p.z>q.z;});
 static const char*LB[3]={"X","Y","Z"};
 for(auto&e:d){const float*c=AC[e.a];float k=e.pos?1.f:.5f,r=e.pos?H*.024f:H*.017f;
  if(e.pos)for(int j=1;j<6;j++)rect(cx+(e.x-cx)*j/6-2,cy+(e.y-cy)*j/6-2,4,4,c[0],c[1],c[2],1,2);
  rect(e.x-r,e.y-r,2*r,2*r,c[0]*k,c[1]*k,c[2]*k,1,r);
  if(e.pos){float ps=H*.0055f;text(LB[e.a],e.x-tw(LB[e.a],ps)/2,e.y-2.5f*ps,ps,1,1,1);}}}
// ---------- exportacao (MAD / glTF) + rigging ----------
bool parentMode=false;std::string gToast;float gToastT=0;const char*gDir=".";
void toast(const std::string&t){gToast=t;gToastT=4;}
std::string fm(const char*f,...){char b[1024];va_list a;va_start(a,f);vsnprintf(b,1024,f,a);va_end(a);return b;}
void insertKey(){if(sel<0)return;Obj&o=objs[sel];bool f=false;for(auto&k:o.k)if(fabsf(k.t-tm)<.02f){k.x=o.cur;f=true;}
 if(!f){o.k.push_back({tm,o.cur});std::sort(o.k.begin(),o.k.end(),[](const Key&a,const Key&b){return a.t<b.t;});}}
void setParent(int c,int p){for(int a=p;a>=0;a=objs[a].parent)if(a==c){toast("Nao pode: ciclo");return;}
 V w=wp(c);objs[c].parent=p;objs[c].cur.p=invPt(worldM(p),w);toast("Parent definido");}
void finishParent(int h){parentMode=false;if(sel>=0&&h>=0&&h!=sel)setParent(sel,h);else toast("Cancelado");}
FILE*openOut(const char*ext,std::string&path,bool&fb){long t=(long)time(nullptr);fb=false;
 path=fm("/storage/emulated/0/Download/nomad_%ld.%s",t,ext);FILE*f=fopen(path.c_str(),"wb");
 if(!f){path=fm("%s/nomad_%ld.%s",gDir,t,ext);f=fopen(path.c_str(),"wb");fb=true;}return f;}
void saved(const std::string&path,bool fb){toast("Salvo: "+path+(fb?"  (ative Acesso a todos os arquivos para salvar em Downloads)":""));}
void exportMAD(){std::string path;bool fb;FILE*f=openOut("mad",path,fb);if(!f){toast("Erro ao salvar");return;}
 auto U_=[&](uint32_t v){fwrite(&v,4,1,f);};auto Fl=[&](float v){fwrite(&v,4,1,f);};
 fwrite("MAD1",1,4,f);U_(1);Fl(24);Fl(DUR);U_((uint32_t)objs.size());
 for(auto&o:objs){U_((uint32_t)o.mesh);U_((uint32_t)o.parent);Fl(o.len);Fl(o.col.x);Fl(o.col.y);Fl(o.col.z);
  const float*c=&o.cur.p.x;for(int i=0;i<9;i++)Fl(c[i]);
  U_((uint32_t)o.k.size());for(auto&k:o.k){Fl(k.t);const float*q=&k.x.p.x;for(int i=0;i<9;i++)Fl(q[i]);}}
 fclose(f);saved(path,fb);}
std::string b64(const std::vector<unsigned char>&d){static const char*AB="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";std::string o;
 for(size_t i=0;i<d.size();i+=3){unsigned v=d[i]<<16;if(i+1<d.size())v|=d[i+1]<<8;if(i+2<d.size())v|=d[i+2];
  o+=AB[v>>18&63];o+=AB[v>>12&63];o+=i+1<d.size()?AB[v>>6&63]:'=';o+=i+2<d.size()?AB[v&63]:'=';}return o;}
void qm(const float*a,const float*b,float*o){o[0]=a[3]*b[0]+a[0]*b[3]+a[1]*b[2]-a[2]*b[1];o[1]=a[3]*b[1]-a[0]*b[2]+a[1]*b[3]+a[2]*b[0];
 o[2]=a[3]*b[2]+a[0]*b[1]-a[1]*b[0]+a[2]*b[3];o[3]=a[3]*b[3]-a[0]*b[0]-a[1]*b[1]-a[2]*b[2];}
void eq(V r,float*q){float a[4]={sinf(r.x/2),0,0,cosf(r.x/2)},b[4]={0,sinf(r.y/2),0,cosf(r.y/2)},c[4]={0,0,sinf(r.z/2),cosf(r.z/2)},t[4];qm(b,a,t);qm(c,t,q);}
std::string mm3(const std::vector<float>&v){float lo[3]={1e30f,1e30f,1e30f},hi[3]={-1e30f,-1e30f,-1e30f};
 for(size_t i=0;i+2<v.size();i+=3)for(int c=0;c<3;c++){lo[c]=std::min(lo[c],v[i+c]);hi[c]=std::max(hi[c],v[i+c]);}
 return fm(",\"min\":[%g,%g,%g],\"max\":[%g,%g,%g]",lo[0],lo[1],lo[2],hi[0],hi[1],hi[2]);}
void exportGLTF(){
 if(objs.empty()){toast("Cena vazia");return;}
 std::string path;bool fb;FILE*f=openOut("gltf",path,fb);if(!f){toast("Erro ao salvar");return;}
 std::vector<unsigned char> bin;std::string views,accs,meshJ,mats,nodes,samp,chn,roots;int nv=0,na=0,nm=0,ns=0;
 auto view=[&](const void*d,size_t n){while(bin.size()%4)bin.push_back(0);size_t off=bin.size();const unsigned char*c=(const unsigned char*)d;bin.insert(bin.end(),c,c+n);
  views+=fm("%s{\"buffer\":0,\"byteOffset\":%zu,\"byteLength\":%zu}",nv?",":"",off,n);return nv++;};
 auto acc=[&](const std::vector<float>&v,int comps,const char*ty,const std::string&mm){int vi=view(v.data(),v.size()*4);
  accs+=fm("%s{\"bufferView\":%d,\"componentType\":5126,\"count\":%d,\"type\":\"%s\"%s}",na?",":"",vi,(int)v.size()/comps,ty,mm.c_str());return na++;};
 int pa[3]={-1,-1,-1},pn[3]={-1,-1,-1};
 for(int i=0;i<(int)objs.size();i++){Obj&o=objs[i];int mj=-1;bool bone=o.mesh==5;
  if(o.mesh<3){int m=o.mesh;
   if(pa[m]<0){std::vector<float> P,N;auto&c=meshes[m].cpu;for(size_t j=0;j+5<c.size();j+=6){P.insert(P.end(),{c[j],c[j+1],c[j+2]});N.insert(N.end(),{c[j+3],c[j+4],c[j+5]});}
    pa[m]=acc(P,3,"VEC3",mm3(P));pn[m]=acc(N,3,"VEC3","");}
   mats+=fm("%s{\"pbrMetallicRoughness\":{\"baseColorFactor\":[%g,%g,%g,1],\"metallicFactor\":0,\"roughnessFactor\":0.8}}",nm?",":"",o.col.x,o.col.y,o.col.z);
   meshJ+=fm("%s{\"primitives\":[{\"attributes\":{\"POSITION\":%d,\"NORMAL\":%d},\"material\":%d}]}",nm?",":"",pa[m],pn[m],nm);mj=nm++;}
  float q[4];eq(o.cur.r,q);std::string ch;
  for(int j=0;j<(int)objs.size();j++)if(objs[j].parent==i)ch+=fm("%s%d",ch.empty()?"":",",j);
  std::string n=fm("{\"name\":\"%s\",\"translation\":[%g,%g,%g],\"rotation\":[%g,%g,%g,%g],\"scale\":[%g,%g,%g]",o.nm,
   o.cur.p.x,o.cur.p.y,o.cur.p.z,q[0],q[1],q[2],q[3],o.cur.s.x,o.cur.s.y,o.cur.s.z);
  if(mj>=0)n+=fm(",\"mesh\":%d",mj);if(bone)n+=fm(",\"extras\":{\"bone\":true,\"length\":%g}",o.len);
  if(!ch.empty())n+=",\"children\":["+ch+"]";n+="}";nodes+=(i?",":"")+n;
  if(o.parent<0)roots+=fm("%s%d",roots.empty()?"":",",i);}
 for(int i=0;i<(int)objs.size();i++){Obj&o=objs[i];if(o.k.empty())continue;std::vector<float> ti,tp,rq,sc;
  for(auto&k:o.k){ti.push_back(k.t);tp.insert(tp.end(),{k.x.p.x,k.x.p.y,k.x.p.z});float q[4];eq(k.x.r,q);rq.insert(rq.end(),{q[0],q[1],q[2],q[3]});sc.insert(sc.end(),{k.x.s.x,k.x.s.y,k.x.s.z});}
  int ai=acc(ti,1,"SCALAR",fm(",\"min\":[%g],\"max\":[%g]",ti.front(),ti.back()));
  int ao[3]={acc(tp,3,"VEC3",""),acc(rq,4,"VEC4",""),acc(sc,3,"VEC3","")};static const char*PN[3]={"translation","rotation","scale"};
  for(int c=0;c<3;c++){samp+=fm("%s{\"input\":%d,\"output\":%d,\"interpolation\":\"LINEAR\"}",ns?",":"",ai,ao[c]);
   chn+=fm("%s{\"sampler\":%d,\"target\":{\"node\":%d,\"path\":\"%s\"}}",ns?",":"",ns,i,PN[c]);ns++;}}
 std::string js="{\"asset\":{\"version\":\"2.0\",\"generator\":\"Nomad Animator\"},\"scene\":0,\"scenes\":[{\"nodes\":["+roots+"]}],\"nodes\":["+nodes+"],";
 if(nm)js+="\"meshes\":["+meshJ+"],\"materials\":["+mats+"],";
 if(ns)js+="\"animations\":[{\"name\":\"Anim\",\"samplers\":["+samp+"],\"channels\":["+chn+"]}],";
 js+="\"accessors\":["+accs+"],\"bufferViews\":["+views+"],\"buffers\":[{\"byteLength\":"+std::to_string(bin.size())+",\"uri\":\"data:application/octet-stream;base64,"+b64(bin)+"\"}]}";
 fwrite(js.data(),1,js.size(),f);fclose(f);saved(path,fb);}
void frame(){
 glViewport(0,0,W,H);glClearColor(.24f,.24f,.26f,1);glClear(GL_COLOR_BUFFER_BIT|GL_DEPTH_BUFFER_BIT);
 glEnable(GL_DEPTH_TEST);
 gVP=mul(persp(FOV,(float)W/H,.1f,100),lookAt(camEye(),tgt,{0,1,0}));
 draw(meshes[4],gVP,id(),.34f,.34f,.37f,1,0);
 auto ln=[&](V c,V sc,float r,float g,float b){T t;t.p=c;t.s=sc;M m=model(t);draw(meshes[0],mul(gVP,m),m,r,g,b,1,0);};
 ln({0,0,0},{20,.014f,.014f},.85f,.28f,.3f);ln({0,0,0},{.014f,.014f,20},.3f,.5f,.9f);
 for(int i=0;i<(int)objs.size();i++){Obj&o=objs[i];M mod=worldM(i);if(o.mesh==5){float wd=o.len*.45f;for(int k=0;k<4;k++){mod.m[k]*=wd;mod.m[4+k]*=o.len;mod.m[8+k]*=wd;}}float h=(i==sel)?.35f:0;
  draw(meshes[o.mesh],mul(gVP,mod),mod,o.col.x+(1-o.col.x)*h,o.col.y+(1-o.col.y)*h,o.col.z+(1-o.col.z)*h,1,1);}
 glDisable(GL_DEPTH_TEST);
 if(sel>=0&&tool<3)drawGizmo();
 gBtn.clear();gBlock.clear();float u=U(),ML_=ML(),hH=7.2f*u;
 // cabecalho
 rect(0,0,W,hH,.15f,.15f,.16f,.96f);gBlock.push_back({0,0,(float)W,hH});
 float x=ML_,ph=5*u,py=(hH-ph)/2,ps=ph*.072f,tp=ph*.07f;
 text("Nomad Animator v5",x,hH/2-2.5f*tp,tp,.65f,.65f,.7f);x+=tw("Nomad Animator v5",tp)+3*u;
 const char*ad[8]={"+ Cube","+ Sphere","+ Plane","+ Bone","Parent","Unparent","Export MAD","Export glTF"};const int aid[8]={0,1,2,10,11,12,13,14};
 for(int i=0;i<8;i++){float w=tw(ad[i],ps)+4*u;pill(x,py,w,ph,aid[i],ad[i],false,i<4?.22f:i<7?.3f:.5f,i<4?.42f:i<7?.32f:.36f,i<4?.3f:i<7?.38f:.12f);x+=w+.8f*u;}
 {const char*d="Delete";float w=tw(d,ps)+4*u;pill(W-ML_-w,py,w,ph,9,d,false,.5f,.2f,.2f);}
 // barra de ferramentas (esquerda)
 float ts=8*u,tx0=ML_,ty0=hH+1.5f*u;const int TID[4]={6,3,4,5};
 panel(tx0,ty0,ts+1.2f*u,4*ts+3*.8f*u+1.2f*u,1*u);
 for(int k=0;k<4;k++){float bx=tx0+.6f*u,by=ty0+.6f*u+k*(ts+.8f*u);bool on=(tool==TID[k]-3);
  rect(bx,by,ts,ts,on?.28f:.33f,on?.45f:.33f,on?.7f:.35f,1,1*u);icon(TID[k],bx+ts/2,by+ts/2,ts*.26f,on);gBtn.push_back({{bx,by,ts,ts},TID[k]});}
 // outliner + transform (direita)
 float pw=30*u,rx=W-ML_-pw,ry=navY()+navR()+1.5f*u,rh=4.4f*u,tpx=.38f*u;
 int n=(int)objs.size(),rows=std::min(n,4),st=(n>4&&sel>=0)?std::clamp(sel-3,0,n-4):0;
 float oh=4*u+std::max(rows,1)*rh+1*u;panel(rx,ry,pw,oh,1*u);
 text("Scene",rx+1.5f*u,ry+2*u-2.5f*tpx,tpx,.6f,.6f,.65f);
 if(!n)text("Empty - tap + Cube",rx+1.5f*u,ry+4*u+2.2f*u-2.5f*tpx,tpx,.5f,.5f,.55f);
 for(int r=0;r<rows;r++){int i=st+r;float yy=ry+4*u+r*rh;
  if(i==sel)rect(rx+.6f*u,yy,pw-1.2f*u,rh-.2f*u,.28f,.45f,.7f,1,.7f*u);
  rect(rx+1.6f*u,yy+1.3f*u,1.8f*u,1.8f*u,objs[i].col.x,objs[i].col.y,objs[i].col.z,1,.9f*u);
  text(objs[i].nm,rx+4.6f*u,yy+2.2f*u-2.5f*tpx,tpx,.93f,.93f,.93f);gBtn.push_back({{rx,yy,pw,rh},100+i});}
 if(sel>=0){T&t=objs[sel].cur;float ty=ry+oh+1.5f*u;panel(rx,ty,pw,4*u+3*rh+1*u,1*u);
  text("Transform",rx+1.5f*u,ty+2*u-2.5f*tpx,tpx,.6f,.6f,.65f);
  float lw=5.5f*u,fw=(pw-lw-1.2f*u)/3;static const char*XYZ[3]={"X","Y","Z"};
  for(int j=0;j<3;j++)tcen(XYZ[j],rx+lw+j*fw+fw/2,ty+2*u,tpx,AC[j][0],AC[j][1],AC[j][2]);
  static const char*LB3[3]={"Loc","Rot","Scl"};V val[3]={t.p,t.r*(180/PI),t.s};
  for(int k=0;k<3;k++){float yy=ty+4*u+k*rh;text(LB3[k],rx+1.2f*u,yy+2.2f*u-2.5f*tpx,tpx,.75f,.75f,.78f);
   for(int j=0;j<3;j++){char b[16];snprintf(b,16,k==1?"%.1f":"%.2f",(&val[k].x)[j]);float fx=rx+lw+j*fw;
    rect(fx,yy+.3f*u,fw-.5f*u,rh-.6f*u,.25f,.25f,.27f,1,.6f*u);tcen(b,fx+(fw-.5f*u)/2,yy+2.2f*u,tpx*.95f,.92f,.92f,.92f);}}}
 // timeline
 float tT=100*u-3.6f*u-18*u,tw_=W-2*ML_;panel(ML_,tT,tw_,18*u,1*u);
 {float sy=tT+.7f*u,sh_=4.8f*u,pp=sh_*.072f;const char*pl=playing?"Pause":"Play";
  float w1=tw(pl,pp)+5*u;pill(ML_+.8f*u,sy,w1,sh_,8,pl,playing,.33f,.33f,.35f);
  float w2=tw("Key",pp)+5*u;pill(ML_+1.6f*u+w1,sy,w2,sh_,7,"Key",false,.62f,.5f,.1f);
  char b[24];snprintf(b,24,"Frame %d / %d",(int)roundf(tm*24),(int)(DUR*24));text(b,ML_+tw_-tw(b,pp)-1.5f*u,sy+sh_/2-2.5f*pp,pp,.85f,.85f,.88f);}
 gTrack={ML_,tT+6.4f*u,tw_,11*u};float y0=gTrack.y,h=gTrack.h;gBlock.push_back(gTrack);
 rect(ML_+.6f*u,y0,tw_-1.2f*u,h,.09f,.09f,.1f,1,.8f*u);
 for(int f=0;f<=(int)(DUR*24);f+=6){float xx=tx(f/24.f);bool big=f%24==0;
  rect(xx-.1f*u,y0+(big?3.6f:4.6f)*u,.2f*u,(big?2.2f:1.2f)*u,.5f,.5f,.55f);
  if(big){char b[8];snprintf(b,8,"%d",f);tcen(b,xx,y0+1.8f*u,.34f*u,.7f,.7f,.75f);}}
 if(sel>=0)for(auto&k:objs[sel].k)dia(tx(k.t),y0+8*u,3.4f*u,.98f,.74f,.18f);
 {float px=tx(tm);rect(px-.17f*u,y0,.34f*u,h,.28f,.45f,.7f);rect(px-2.4f*u,y0,4.8f*u,3.2f*u,.28f,.45f,.7f,1,.8f*u);
  char b[8];snprintf(b,8,"%d",(int)roundf(tm*24));tcen(b,px,y0+1.6f*u,.36f*u,1,1,1);}
 if(gToastT>0){float tt=.4f*u,w2=tw(gToast.c_str(),tt)+4*u,bx=(W-w2)/2,by=tT-7*u;rect(bx,by,w2,5.4f*u,.08f,.08f,.08f,.93f,1*u);text(gToast.c_str(),bx+2*u,by+2.7f*u-2.5f*tt,tt,1,1,1);}
 drawNav();
 eglSwapBuffers(dpy,surf);}

// ---------- input ----------
void press(int i){
 if(i<3)addObj(i);else if(i<7)tool=i-3;
 else if(i==7)insertKey();else if(i==8)playing=!playing;
 else if(i==9){if(sel>=0)delObj(sel);}
 else if(i==10)addObj(5);
 else if(i==11){if(sel<0)toast("Selecione um objeto");else{parentMode=true;toast("Toque no objeto PAI");}}
 else if(i==12){if(sel>=0)clearParent(sel);}
 else if(i==13)exportMAD();else if(i==14)exportGLTF();}
void scrub(float x){tm=roundf(std::clamp((x-ML())/(W-2*ML()),0.f,1.f)*DUR*24)/24;applyAnim();}
void pick(float x,float y){
 V e=camEye(),f=norm(tgt-e),s2=norm(cross(f,V{0,1,0})),u=cross(s2,f);
 float th=tanf(FOV/2),as=(float)W/H;V d=norm(f+s2*((2*x/W-1)*th*as)+u*((1-2*y/H)*th));
 static const float RF[3]={.87f,.5f,1.42f};int best=-1;float bt=1e9f;
 for(int i=0;i<(int)objs.size();i++){Obj&o=objs[i];V c=wp(i);float r;
  if(o.mesh==5){M w=worldM(i);c=c+V{w.m[4],w.m[5],w.m[6]}*(o.len*.5f);r=o.len*.35f;}
  else r=RF[o.mesh]*std::max({o.cur.s.x,o.cur.s.y,o.cur.s.z});
  V oc=e-c;float b=dot(oc,d),cc=dot(oc,oc)-r*r,ds=b*b-cc;if(ds<0)continue;
  float tt=-b-sqrtf(ds);if(tt>0&&tt<bt){bt=tt;best=i;}}
 if(parentMode)finishParent(best);else sel=best;}
void orbit(float dx,float dy){yaw-=dx*.006f;pitch=std::clamp(pitch+dy*.006f,-1.5f,1.5f);}
void gdrag(float dx,float dy){
 Obj&ob=objs[sel];T&t=ob.cur;V o=wp(sel);float ox,oy,ex,ey;
 if(tool==1){float px,py,qx,qy;if(!prj(ringPt(gAxis,gIdx+1),px,py)||!prj(ringPt(gAxis,gIdx+31),qx,qy))return;
  float vx=px-qx,vy=py-qy,l=hypotf(vx,vy);if(l<1)return;(&t.r.x)[gAxis]+=(dx*vx+dy*vy)/l*.012f;return;}
 if(!prj(o,ox,oy)||!prj(o+AX[gAxis]*gl(),ex,ey))return;
 float vx=ex-ox,vy=ey-oy,k=(dx*vx+dy*vy)/(vx*vx+vy*vy+1e-3f);
 if(tool==0){V nw=o+AX[gAxis]*(k*gl());t.p=ob.parent>=0?invPt(worldM(ob.parent),nw):nw;}
 else if(ob.mesh==5)ob.len=std::max(.05f,ob.len*(1+k));
 else{float&sc=(&t.s.x)[gAxis];sc=std::max(.05f,sc*(1+k));}}
void snap(float x,float y){ND d[6];navPts(d);
 for(auto&e:d)if(hypotf(x-e.x,y-e.y)<H*.035f){
  if(e.a==0){yaw=e.pos?PI/2:-PI/2;pitch=0;}else if(e.a==1)pitch=e.pos?1.45f:-1.45f;else{yaw=e.pos?0.f:PI;pitch=0;}return;}}
int32_t onInput(android_app*,AInputEvent*e){
 static int mode=0;static float lx,ly,sx,sy,pinch;static bool moved,rl;
 if(AInputEvent_getType(e)!=AINPUT_EVENT_TYPE_MOTION)return 0;
 int act=AMotionEvent_getAction(e)&AMOTION_EVENT_ACTION_MASK,n=(int)AMotionEvent_getPointerCount(e);
 float x=AMotionEvent_getX(e,0),y=AMotionEvent_getY(e,0);
 if(act==AMOTION_EVENT_ACTION_DOWN){
  moved=false;rl=true;sx=x;sy=y;pinch=0;gDrag=false;mode=-1;
  for(auto&b:gBtn)if(inR(b.r,x,y)){if(b.id>=100){if(parentMode)finishParent(b.id-100);else sel=b.id-100;}else press(b.id);mode=2;break;}
  if(mode<0){
   if(inR(gTrack,x,y)){mode=3;scrub(x);}
   else if(hypotf(x-navX(),y-navY())<navR()+12)mode=4;
   else{bool blk=false;for(auto&r:gBlock)if(inR(r,x,y))blk=true;
    if(blk)mode=2;else{int a=hitGizmo(x,y);if(a>=0){gAxis=a;gDrag=true;mode=5;}else mode=1;}}}
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
 if(app->activity)gDir=app->activity->externalDataPath?app->activity->externalDataPath:app->activity->internalDataPath;
 auto now=[](){timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;};
 double last=now();
 while(true){
  int ev;android_poll_source*src;
  while(ALooper_pollOnce(ready?0:-1,nullptr,&ev,(void**)&src)>=0){
   if(src)src->process(app,src);
   if(app->destroyRequested){termEGL();return;}}
  if(ready){double t=now();float dt=(float)(t-last);last=t;gToastT-=dt;
   if(playing){tm+=dt;if(tm>DUR)tm=0;applyAnim();}
   frame();}else last=now();}}
