// Nomad Animator - editor/animador 3D em C++ + OpenGL ES 3.0 (NativeActivity)
// Interface estilo Blender adaptada para celular + import glTF rigs + export .MAD
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
#include <string>
#include <fstream>
#include <sstream>
#include <sys/stat.h>
#include <unistd.h>
#include <dirent.h>
#include <map>
#include <cctype>
#define STB_TRUETYPE_IMPLEMENTATION
#include "stb_truetype.h"
#define PI 3.14159265f
#define LOGI(...) __android_log_print(ANDROID_LOG_INFO,"Nomad",__VA_ARGS__)
#define LOGE(...) __android_log_print(ANDROID_LOG_ERROR,"Nomad",__VA_ARGS__)

// ---------- matematica ----------
struct V{float x=0,y=0,z=0;};
V operator+(V a,V b){return{a.x+b.x,a.y+b.y,a.z+b.z};}
V operator-(V a,V b){return{a.x-b.x,a.y-b.y,a.z-b.z};}
V operator*(V a,float k){return{a.x*k,a.y*k,a.z*k};}
float dot(V a,V b){return a.x*b.x+a.y*b.y+a.z*b.z;}
V cross(V a,V b){return{a.y*b.z-a.z*b.y,a.z*b.x-a.x*b.z,a.x*b.y-a.y*b.x};}
V norm(V a){float l=sqrtf(dot(a,a));return l>1e-8f?a*(1.f/l):V{0,1,0};}
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
struct Obj{int mesh;V col;T cur;std::vector<Key> k;std::string name;};
std::vector<Obj> objs;

struct Bone{
 std::string name;
 int parent=-1;
 V head{0,0,0},tail{0,1,0};
 T pose; // pose mode transform (local)
 bool selected=false;
};
struct Armature{
 std::string name="Armature";
 std::vector<Bone> bones;
 bool visible=true;
};
std::vector<Armature> rigs;

enum Screen{HOME=0,EDITOR=1,FILE_BROWSER=2};
Screen screen=HOME;
enum EditorMode{OBJECT_MODE=0,EDIT_MODE=1,POSE_MODE=2};
EditorMode editorMode=OBJECT_MODE;
std::string projectName="Untitled Project",projectStatus="Ready";
int panelMode=0;
bool showOutliner=true,showProperties=true,showToolShelf=true;
int selBone=-1,selRig=-1;
int sel=-1,tool=0,W=1,H=1; // tool: 0=Move(G),1=Rotate(R),2=Scale(S),3=Camera
bool playing=false;float tm=0;const float DUR=5.f;
float yaw=.6f,pitch=.4f,cd=8;V tgt{0,.8f,0};const float FOV=1.047f;
V camEye(){return tgt+V{cosf(pitch)*sinf(yaw),sinf(pitch),cosf(pitch)*cosf(yaw)}*cd;}
int fileBrowserMode=0; // 0=open mad, 1=import gltf, 2=save as
std::vector<std::string> browserFiles;
int browserSel=-1;

T eval(Obj&o,float t){
 auto&k=o.k;if(k.empty())return o.cur;
 if(t<=k.front().t)return k.front().x;if(t>=k.back().t)return k.back().x;
 size_t i=0;while(i+1<k.size()&&k[i+1].t<t)i++;
 float u=(t-k[i].t)/(k[i+1].t-k[i].t);T r;
 r.p=lerp(k[i].x.p,k[i+1].x.p,u);r.r=lerp(k[i].x.r,k[i+1].x.r,u);r.s=lerp(k[i].x.s,k[i+1].x.s,u);return r;}
void applyAnim(){for(auto&o:objs)if(!o.k.empty())o.cur=eval(o,tm);}
void addObj(int mesh){
 static const V pal[]={{.9f,.35f,.3f},{.3f,.7f,.9f},{.5f,.85f,.4f},{.95f,.8f,.3f},{.7f,.45f,.9f}};
 Obj o;o.mesh=mesh;o.col=pal[objs.size()%5];
 o.name=mesh==0?"Cube":mesh==1?"Sphere":"Plane";
 o.cur.p={(objs.size()%4)*1.4f-2.1f,mesh==2?0.f:.5f,0};
 if(mesh==2)o.cur.s={2,2,2};
 objs.push_back(o);sel=(int)objs.size()-1;selBone=-1;}

// ---------- projetos, .MAD e glTF ----------
std::string dataRoot(){return std::string("/sdcard/Android/data/com.nomad.animator/files/");}
void ensureDir(){
 mkdir("/sdcard",0777);mkdir("/sdcard/Android",0777);mkdir("/sdcard/Android/data",0777);
 mkdir("/sdcard/Android/data/com.nomad.animator",0777);mkdir(dataRoot().c_str(),0777);}
std::vector<std::string> recentProjects;
void scanProjects(){
 recentProjects.clear();ensureDir();
 if(DIR*dr=opendir(dataRoot().c_str())){
  while(dirent*en=readdir(dr)){std::string n=en->d_name;
   if(n.size()>4&&n.substr(n.size()-4)==".mad")recentProjects.push_back(n.substr(0,n.size()-4));}
  closedir(dr);}
 std::sort(recentProjects.begin(),recentProjects.end());
 if(recentProjects.size()>8)recentProjects.resize(8);}
void scanBrowser(const char*ext){
 browserFiles.clear();browserSel=-1;ensureDir();
 if(DIR*dr=opendir(dataRoot().c_str())){
  while(dirent*en=readdir(dr)){std::string n=en->d_name;
   if(n.size()>strlen(ext)&&n.substr(n.size()-strlen(ext))==ext)browserFiles.push_back(n);}
  closedir(dr);}
 std::sort(browserFiles.begin(),browserFiles.end());}
std::string safeProjectName(){std::string n=projectName;for(char&c:n)if(c=='/'||c=='\\'||c==':'||c=='.')c='_';return n.empty()?"Untitled":n;}
std::string madPath(){ensureDir();return dataRoot()+safeProjectName()+".mad";}
std::string gltfPath(){ensureDir();return dataRoot()+safeProjectName()+".gltf";}

void newProject(){
 objs.clear();rigs.clear();sel=-1;selBone=-1;selRig=-1;tm=0;playing=false;
 editorMode=OBJECT_MODE;projectName="Untitled Project";projectStatus="New project";
 addObj(0);if(!objs.empty())objs[0].cur.p={0,.5f,0};}

void saveMAD(){
 ensureDir();
 std::ofstream f(madPath()); if(!f){projectStatus="Save failed - check storage permission";return;}
 f<<"NOMAD_ANIMATOR_MAD 3\n"<<projectName<<"\n";
 f<<objs.size()<<" "<<rigs.size()<<"\n";
 for(auto&o:objs){
  f<<"OBJ "<<o.name<<" "<<o.mesh<<" "<<o.col.x<<" "<<o.col.y<<" "<<o.col.z<<" "
   <<o.cur.p.x<<" "<<o.cur.p.y<<" "<<o.cur.p.z<<" "
   <<o.cur.r.x<<" "<<o.cur.r.y<<" "<<o.cur.r.z<<" "
   <<o.cur.s.x<<" "<<o.cur.s.y<<" "<<o.cur.s.z<<" "<<o.k.size()<<"\n";
  for(auto&k:o.k)f<<"K "<<k.t<<" "<<k.x.p.x<<" "<<k.x.p.y<<" "<<k.x.p.z<<" "
   <<k.x.r.x<<" "<<k.x.r.y<<" "<<k.x.r.z<<" "<<k.x.s.x<<" "<<k.x.s.y<<" "<<k.x.s.z<<"\n";
 }
 for(auto&r:rigs){
  f<<"RIG "<<r.name<<" "<<r.bones.size()<<" "<<(r.visible?1:0)<<"\n";
  for(auto&b:r.bones)
   f<<"B "<<b.name<<" "<<b.parent<<" "
    <<b.head.x<<" "<<b.head.y<<" "<<b.head.z<<" "
    <<b.tail.x<<" "<<b.tail.y<<" "<<b.tail.z<<" "
    <<b.pose.p.x<<" "<<b.pose.p.y<<" "<<b.pose.p.z<<" "
    <<b.pose.r.x<<" "<<b.pose.r.y<<" "<<b.pose.r.z<<"\n";
 }
 f.close();
 projectStatus="Saved: "+safeProjectName()+".mad";scanProjects();
}

void loadMAD(const std::string&base){
 std::ifstream f(dataRoot()+base+".mad");if(!f){projectStatus="Could not open "+base+".mad";return;}
 std::string magic,line;std::getline(f,magic);
 if(magic.find("NOMAD_ANIMATOR_MAD")!=0){projectStatus="Invalid .MAD file";return;}
 std::getline(f,projectName);
 size_t no=0,nr=0;f>>no>>nr;std::getline(f,line);
 objs.clear();rigs.clear();
 for(size_t i=0;i<no;i++){
  Obj o;std::string tag;f>>tag>>o.name>>o.mesh>>o.col.x>>o.col.y>>o.col.z
   >>o.cur.p.x>>o.cur.p.y>>o.cur.p.z>>o.cur.r.x>>o.cur.r.y>>o.cur.r.z
   >>o.cur.s.x>>o.cur.s.y>>o.cur.s.z;size_t nk=0;f>>nk;std::getline(f,line);
  for(size_t j=0;j<nk;j++){Key k;std::string kt;f>>kt>>k.t>>k.x.p.x>>k.x.p.y>>k.x.p.z
   >>k.x.r.x>>k.x.r.y>>k.x.r.z>>k.x.s.x>>k.x.s.y>>k.x.s.z;std::getline(f,line);o.k.push_back(k);}
  objs.push_back(o);
 }
 for(size_t i=0;i<nr;i++){
  Armature a;std::string tag;size_t nb=0;int vis=1;f>>tag>>a.name>>nb>>vis;a.visible=vis;std::getline(f,line);
  for(size_t j=0;j<nb;j++){
   Bone b;std::string bt;f>>bt>>b.name>>b.parent
    >>b.head.x>>b.head.y>>b.head.z>>b.tail.x>>b.tail.y>>b.tail.z
    >>b.pose.p.x>>b.pose.p.y>>b.pose.p.z>>b.pose.r.x>>b.pose.r.y>>b.pose.r.z;
   std::getline(f,line);a.bones.push_back(b);}
  rigs.push_back(a);
 }
 sel=objs.empty()?-1:0;selBone=-1;selRig=rigs.empty()?-1:0;
 tm=0;playing=false;screen=EDITOR;editorMode=OBJECT_MODE;
 projectStatus="Opened: "+base+".mad";
}

// ---------- glTF import (rigs / skins) ----------
// Minimal string-based parser focused on nodes + skins (armatures)
static std::string extractJsonString(const std::string&src,size_t pos){
 if(pos>=src.size()||src[pos]!='"')return "";
 size_t e=pos+1;while(e<src.size()&&src[e]!='"'){if(src[e]=='\\')e++;e++;}
 return src.substr(pos+1,e-pos-1);}
static float extractJsonNumber(const std::string&src,size_t&pos){
 while(pos<src.size()&&(src[pos]==' '||src[pos]==','||src[pos]==':'||src[pos]=='['||src[pos]=='{'))pos++;
 size_t s=pos;while(pos<src.size()&&(isdigit(src[pos])||src[pos]=='.'||src[pos]=='-'||src[pos]=='+'||src[pos]=='e'||src[pos]=='E'))pos++;
 return s<pos?(float)atof(src.substr(s,pos-s).c_str()):0.f;}
static std::vector<int> extractJsonIntArray(const std::string&src,size_t pos){
 std::vector<int> out;size_t p=src.find('[',pos);if(p==std::string::npos)return out;
 p++;while(p<src.size()&&src[p]!=']'){while(p<src.size()&&!isdigit(src[p])&&src[p]!='-'&&src[p]!=']')p++;
  if(p>=src.size()||src[p]==']')break;int v=(int)extractJsonNumber(src,p);out.push_back(v);}
 return out;}
static std::vector<float> extractJsonFloatArray(const std::string&src,size_t pos){
 std::vector<float> out;size_t p=src.find('[',pos);if(p==std::string::npos)return out;
 p++;while(p<src.size()&&src[p]!=']'){while(p<src.size()&&!isdigit(src[p])&&src[p]!='-'&&src[p]!='.'&&src[p]!=']')p++;
  if(p>=src.size()||src[p]==']')break;out.push_back(extractJsonNumber(src,p));}
 return out;}

struct GltfNode{std::string name;int parent=-1;V translation{0,0,0};V rotation{0,0,0};V scale{1,1,1};std::vector<int> children;};
void importGLTF(const std::string&filename){
 std::string path=dataRoot()+filename;
 std::ifstream f(path);if(!f){projectStatus="Cannot open "+filename;return;}
 std::stringstream ss;ss<<f.rdbuf();std::string json=ss.str();f.close();
 if(json.empty()){projectStatus="Empty glTF file";return;}

 // Parse nodes
 std::vector<GltfNode> nodes;
 size_t nodesPos=json.find("\"nodes\"");
 if(nodesPos!=std::string::npos){
  size_t arr=json.find('[',nodesPos);
  size_t depth=0,start=arr;
  for(size_t i=arr;i<json.size();i++){
   if(json[i]=='['){if(depth==0)start=i;depth++;}
   else if(json[i]==']'){depth--;if(depth==0){ /* end of nodes array */ break;}}
   else if(json[i]=='{'&&depth==1){
    GltfNode n;
    size_t nameP=json.find("\"name\"",i);
    if(nameP!=std::string::npos&&nameP<i+400){size_t q=json.find('"',nameP+6);n.name=extractJsonString(json,q);}
    else n.name="Node_"+std::to_string(nodes.size());
    size_t tr=json.find("\"translation\"",i);
    if(tr!=std::string::npos&&tr<i+500){auto a=extractJsonFloatArray(json,tr);if(a.size()>=3)n.translation={a[0],a[1],a[2]};}
    size_t sc=json.find("\"scale\"",i);
    if(sc!=std::string::npos&&sc<i+500){auto a=extractJsonFloatArray(json,sc);if(a.size()>=3)n.scale={a[0],a[1],a[2]};}
    size_t ch=json.find("\"children\"",i);
    if(ch!=std::string::npos&&ch<i+600)n.children=extractJsonIntArray(json,ch);
    nodes.push_back(n);
   }
  }
 }

 // Build parent relations
 for(size_t i=0;i<nodes.size();i++)for(int c:nodes[i].children)if(c>=0&&c<(int)nodes.size())nodes[c].parent=(int)i;

 // Parse skins
 std::vector<std::vector<int>> skinsJoints;
 size_t skinsPos=json.find("\"skins\"");
 if(skinsPos!=std::string::npos){
  size_t arr=json.find('[',skinsPos);size_t depth=0;
  for(size_t i=arr;i<json.size();i++){
   if(json[i]=='[')depth++;
   else if(json[i]==']'){depth--;if(depth==0)break;}
   else if(json[i]=='{'&&depth==1){
    size_t jpos=json.find("\"joints\"",i);
    if(jpos!=std::string::npos&&jpos<i+300)skinsJoints.push_back(extractJsonIntArray(json,jpos));
   }
  }
 }

 if(nodes.empty()){projectStatus="No nodes found in glTF";return;}

 // Create armature from first skin or from all nodes that look like bones
 Armature a;a.name=filename.substr(0,filename.find('.'));
 if(a.name.empty())a.name="ImportedRig";
 a.visible=true;

 std::vector<int> jointList;
 if(!skinsJoints.empty())jointList=skinsJoints[0];
 else{ // fallback: use nodes with children or named like bones
  for(size_t i=0;i<nodes.size();i++)jointList.push_back((int)i);
 }

 std::map<int,int> nodeToBone;
 for(size_t bi=0;bi<jointList.size();bi++){
  int ni=jointList[bi];if(ni<0||ni>=(int)nodes.size())continue;
  nodeToBone[ni]=(int)bi;
  Bone b;b.name=nodes[ni].name.empty()?"Bone_"+std::to_string(bi):nodes[ni].name;
  b.parent=-1;
  // head from translation (accumulate roughly)
  b.head=nodes[ni].translation;
  if(nodes[ni].parent>=0&&nodeToBone.count(nodes[ni].parent)){
   // will set parent later
  }
  // default tail
  b.tail=b.head+V{0,0.25f,0};
  a.bones.push_back(b);
 }

 // Set parents and better head/tail using hierarchy
 for(size_t bi=0;bi<jointList.size();bi++){
  int ni=jointList[bi];if(ni<0||ni>=(int)nodes.size())continue;
  int pni=nodes[ni].parent;
  if(pni>=0&&nodeToBone.count(pni))a.bones[bi].parent=nodeToBone[pni];
 }

 // Improve head/tail positions from hierarchy
 for(size_t bi=0;bi<a.bones.size();bi++){
  Bone&b=a.bones[bi];
  if(b.parent>=0&&b.parent<(int)a.bones.size()){
   b.head=a.bones[b.parent].tail;
  }
  // find a child to set tail direction
  bool foundChild=false;
  for(size_t ci=0;ci<a.bones.size();ci++)if(a.bones[ci].parent==(int)bi){
   a.bones[ci].head=b.head+V{0,0.4f,0}; // temporary
   b.tail=a.bones[ci].head;
   foundChild=true;break;
  }
  if(!foundChild)b.tail=b.head+V{0,0.4f,0};
 }

 // Recompute absolute-ish positions
 std::vector<V> absHead(a.bones.size());
 for(size_t i=0;i<a.bones.size();i++){
  if(a.bones[i].parent<0)absHead[i]=a.bones[i].head;
  else absHead[i]=absHead[a.bones[i].parent]+(a.bones[i].head-a.bones[a.bones[i].parent].head);
 }
 for(size_t i=0;i<a.bones.size();i++){
  a.bones[i].head=absHead[i];
  a.bones[i].tail=absHead[i]+V{0,0.35f,0};
  // better: if has child, point to child
  for(size_t c=0;c<a.bones.size();c++)if(a.bones[c].parent==(int)i){
   a.bones[i].tail=absHead[c];break;
  }
 }

 if(a.bones.empty()){projectStatus="No bones extracted from glTF";return;}

 rigs.push_back(a);selRig=(int)rigs.size()-1;selBone=0;sel=-1;
 editorMode=EDIT_MODE;screen=EDITOR;
 projectStatus="Imported rig: "+a.name+" ("+std::to_string(a.bones.size())+" bones)";
}

void exportGLTF(){
 ensureDir();
 std::ofstream f(gltfPath()); if(!f){projectStatus="glTF export failed";return;}
 f<<"{\n  \"asset\":{\"version\":\"2.0\",\"generator\":\"Nomad Animator\"},\n";
 f<<"  \"scene\":0,\n  \"scenes\":[{\"nodes\":[";
 for(size_t i=0;i<objs.size();++i){if(i)f<<',';f<<i;}
 // add armature nodes after objects
 size_t base=objs.size();
 for(size_t r=0;r<rigs.size();r++){if(base+r>0||!objs.empty())f<<',';f<<(base+r);}
 f<<"]}],\n  \"nodes\":[\n";
 for(size_t i=0;i<objs.size();++i){
  auto&o=objs[i];if(i)f<<",\n";
  f<<"    {\"name\":\""<<o.name<<"\",\"translation\":["<<o.cur.p.x<<","<<o.cur.p.y<<","<<o.cur.p.z
   <<"],\"scale\":["<<o.cur.s.x<<","<<o.cur.s.y<<","<<o.cur.s.z<<"]}";
 }
 for(size_t r=0;r<rigs.size();r++){
  if(objs.size()+r>0)f<<",\n";
  auto&arm=rigs[r];
  f<<"    {\"name\":\""<<arm.name<<"\",\"children\":[";
  // simple: list bone indices as children of root armature node (simplified)
  for(size_t b=0;b<arm.bones.size();b++){if(b)f<<',';f<<(int)(objs.size()+rigs.size()+b);}
  f<<"]}";
 }
 // bone nodes
 for(size_t r=0;r<rigs.size();r++){
  auto&arm=rigs[r];
  for(size_t b=0;b<arm.bones.size();b++){
   f<<",\n    {\"name\":\""<<arm.bones[b].name<<"\",\"translation\":["
    <<arm.bones[b].head.x<<","<<arm.bones[b].head.y<<","<<arm.bones[b].head.z<<"]}";
  }
 }
 f<<"\n  ],\n  \"extras\":{\"nomadProject\":\""<<safeProjectName()
  <<"\",\"objects\":"<<objs.size()<<",\"armatures\":"<<rigs.size()<<"}\n}\n";
 projectStatus="Exported: "+safeProjectName()+".gltf";
}

void addRig(){
 Armature a;a.name="Armature";
 if(!rigs.empty())a.name="Armature."+std::to_string(rigs.size());
 Bone b;b.name="Root";b.head={0,0,0};b.tail={0,1.0f,0};
 a.bones.push_back(b);
 // spine example
 Bone s;s.name="Spine";s.parent=0;s.head={0,1.0f,0};s.tail={0,1.6f,0};a.bones.push_back(s);
 Bone h;h.name="Head";h.parent=1;h.head={0,1.6f,0};h.tail={0,2.0f,0};a.bones.push_back(h);
 rigs.push_back(a);selRig=(int)rigs.size()-1;selBone=0;sel=-1;
 editorMode=EDIT_MODE;projectStatus="Armature created";}

void addBone(){
 if(rigs.empty()){addRig();return;}
 if(selRig<0||selRig>=(int)rigs.size())selRig=(int)rigs.size()-1;
 Armature&r=rigs[selRig];
 Bone b;b.name="Bone."+std::to_string(r.bones.size());
 b.parent=selBone;
 if(selBone>=0&&selBone<(int)r.bones.size())b.head=r.bones[selBone].tail;
 else b.head={0,0,0};
 b.tail=b.head+V{0,0.4f,0};
 r.bones.push_back(b);selBone=(int)r.bones.size()-1;
 editorMode=EDIT_MODE;projectStatus="Bone added";}

void deleteSelected(){
 if(editorMode==EDIT_MODE||editorMode==POSE_MODE){
  if(selRig>=0&&selBone>=0&&selRig<(int)rigs.size()){
   Armature&r=rigs[selRig];
   if(selBone<(int)r.bones.size()&&r.bones.size()>1){
    // simple remove (reparent children to grandparent)
    int p=r.bones[selBone].parent;
    for(auto&b:r.bones)if(b.parent==selBone)b.parent=p;
    r.bones.erase(r.bones.begin()+selBone);
    selBone=std::min(selBone,(int)r.bones.size()-1);
    projectStatus="Bone deleted";
   }
  }
 }else if(sel>=0&&sel<(int)objs.size()){
  objs.erase(objs.begin()+sel);sel=std::min(sel,(int)objs.size()-1);
  projectStatus="Object deleted";
 }}

// ---------- GL ----------
const char*VS=R"(#version 300 es
layout(location=0) in vec3 aP; layout(location=1) in vec3 aN;
uniform mat4 uMVP; uniform mat4 uM; out vec3 vN; out vec3 vP;
void main(){gl_Position=uMVP*vec4(aP,1.0); vN=mat3(uM)*aN; vP=aP;})";
const char*FS=R"(#version 300 es
precision highp float; in vec3 vN; in vec3 vP; uniform vec4 uC; uniform float uL; uniform vec3 uS; out vec4 o;
void main(){if(uL<0.0){vec2 q=(vP.xy-.5)*uS.xy;vec2 e=abs(q)-uS.xy*.5+uS.z;float dd=length(max(e,0.0))+min(max(e.x,e.y),0.0)-uS.z;o=vec4(uC.rgb,uC.a*clamp(.5-dd,0.0,1.0));return;} float d=1.0; if(uL>0.5){d=0.22+0.78*max(dot(normalize(vN),normalize(vec3(.35,.85,.4))),0.0);} o=vec4(uC.rgb*d,uC.a);})";
GLuint uMVP,uM,uC,uL,uS,gProg=0;float gS[3]={1,1,0};void initText();
struct Mesh{GLuint vao=0,vbo=0;int n=0;GLenum mode=GL_TRIANGLES;};
Mesh meshes[5];
GLuint sh(GLenum t,const char*s){GLuint h=glCreateShader(t);glShaderSource(h,1,&s,0);glCompileShader(h);GLint ok;glGetShaderiv(h,GL_COMPILE_STATUS,&ok);
 if(!ok){char b[512];glGetShaderInfoLog(h,512,0,b);LOGE("%s",b);}return h;}
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
 GLuint p=gProg=glCreateProgram();glAttachShader(p,sh(GL_VERTEX_SHADER,VS));glAttachShader(p,sh(GL_FRAGMENT_SHADER,FS));
 glLinkProgram(p);glUseProgram(p);
 uMVP=glGetUniformLocation(p,"uMVP");uM=glGetUniformLocation(p,"uM");uC=glGetUniformLocation(p,"uC");uL=glGetUniformLocation(p,"uL");uS=glGetUniformLocation(p,"uS");
 glEnable(GL_BLEND);glBlendFunc(GL_SRC_ALPHA,GL_ONE_MINUS_SRC_ALPHA);buildMeshes();initText();}
void draw(Mesh&m,const M&mvp,const M&mod,float r,float g,float b,float a,float lit){
 glUniformMatrix4fv(uMVP,1,GL_FALSE,mvp.m);glUniformMatrix4fv(uM,1,GL_FALSE,mod.m);
 glUniform4f(uC,r,g,b,a);glUniform1f(uL,lit);glUniform3f(uS,gS[0],gS[1],gS[2]);glBindVertexArray(m.vao);glDrawArrays(m.mode,0,m.n);}

// ---------- UI 2D (Blender-inspired) ----------
void rect(float x,float y,float w,float h,float r,float g,float b,float a=1,float rad=0){
 M m={};m.m[0]=2*w/W;m.m[5]=-2*h/H;m.m[10]=1;m.m[12]=2*x/W-1;m.m[13]=1-2*y/H;m.m[15]=1;
 gS[0]=w;gS[1]=h;gS[2]=std::min(rad,std::min(w,h)/2.f);draw(meshes[3],m,id(),r,g,b,a,-1);}
void rectBorder(float x,float y,float w,float h,float r,float g,float b,float thick=1.5f){
 rect(x,y,w,thick,r,g,b);rect(x,y+h-thick,w,thick,r,g,b);
 rect(x,y,thick,h,r,g,b);rect(x+w-thick,y,thick,h,r,g,b);}

// Bitmap fallback + TTF
const char*GN="ABCDEHIKLMNOPRSTUVYXZ0123456789";
const char*GG[]={"010101111101101","110101110101110","011100100100011","110101101101110","111100110100111",
 "101101111101101","111010010010111","101101110101101","100100100100111","101111111101101","110101101101101",
 "010101101101010","110101110100100","110101110101101","011100010001110","111010010010010","101101101101111",
 "101101101101010","101101010010010","101101010101101","111001010100111","111101101101111","010110010010111","111001111100111","111001111001111","101101111001001","111100111001111","111100111101111","111001001010010","111101111101111","111101111001111"};
void btext(const char*s,float x,float y,float ps,float r,float g,float b){
 for(;*s;s++){const char*p=strchr(GN,*s);
  if(p){const char*gl=GG[p-GN];for(int k=0;k<15;k++)if(gl[k]=='1')rect(x+(k%3)*ps,y+(k/3)*ps,ps,ps,r,g,b);}
  x+=4*ps;}}
std::vector<unsigned char> gAtlas;stbtt_bakedchar gBC[96];GLuint gTex=0,gTP=0,gTVao=0,gTVbo=0,uTS,uTC;
const float FPX=64;
bool loadFont(){
 FILE*f=nullptr;
 static const char*P[]={"/system/fonts/Roboto-Regular.ttf","/system/fonts/RobotoStatic-Regular.ttf","/system/fonts/Roboto[wdth,wght].ttf","/system/fonts/NotoSans-Regular.ttf","/system/fonts/DroidSans.ttf"};
 for(auto q:P){f=fopen(q,"rb");if(f)break;}
 if(!f){if(DIR*dr=opendir("/system/fonts")){while(dirent*en=readdir(dr)){std::string n=en->d_name;
  if(n.size()>8&&n.find("Roboto")!=std::string::npos&&n.compare(n.size()-4,4,".ttf")==0){f=fopen(("/system/fonts/"+n).c_str(),"rb");if(f)break;}}closedir(dr);}}
 if(!f)return false;
 fseek(f,0,SEEK_END);long sz=ftell(f);fseek(f,0,SEEK_SET);std::vector<unsigned char> d(sz>0?sz:1);
 size_t rd=fread(d.data(),1,sz,f);fclose(f);if(sz<=0||(long)rd!=sz)return false;
 gAtlas.assign(1024*1024,0);
 if(stbtt_BakeFontBitmap(d.data(),0,FPX,gAtlas.data(),1024,1024,32,96,gBC)<=0){gAtlas.clear();return false;}
 return true;}
void initText(){
 static bool tried=false;if(!tried){tried=true;loadFont();}
 gTex=0;if(gAtlas.empty())return;
 const char*vs="#version 300 es\nlayout(location=0) in vec4 aV; uniform vec2 uScr; out vec2 vT;\nvoid main(){gl_Position=vec4(aV.x/uScr.x*2.0-1.0,1.0-aV.y/uScr.y*2.0,0.0,1.0); vT=aV.zw;}";
 const char*fs="#version 300 es\nprecision mediump float; in vec2 vT; uniform sampler2D uTex; uniform vec4 uC; out vec4 o;\nvoid main(){o=vec4(uC.rgb,uC.a*texture(uTex,vT).r);}";
 GLuint p=glCreateProgram();glAttachShader(p,sh(GL_VERTEX_SHADER,vs));glAttachShader(p,sh(GL_FRAGMENT_SHADER,fs));glLinkProgram(p);gTP=p;
 uTS=glGetUniformLocation(p,"uScr");uTC=glGetUniformLocation(p,"uC");glUseProgram(p);glUniform1i(glGetUniformLocation(p,"uTex"),0);glUseProgram(gProg);
 glGenTextures(1,&gTex);glBindTexture(GL_TEXTURE_2D,gTex);glPixelStorei(GL_UNPACK_ALIGNMENT,1);
 glTexImage2D(GL_TEXTURE_2D,0,GL_R8,1024,1024,0,GL_RED,GL_UNSIGNED_BYTE,gAtlas.data());
 glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MIN_FILTER,GL_LINEAR);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MAG_FILTER,GL_LINEAR);
 glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_WRAP_S,GL_CLAMP_TO_EDGE);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_WRAP_T,GL_CLAMP_TO_EDGE);
 glGenVertexArrays(1,&gTVao);glGenBuffers(1,&gTVbo);glBindVertexArray(gTVao);glBindBuffer(GL_ARRAY_BUFFER,gTVbo);
 glEnableVertexAttribArray(0);glVertexAttribPointer(0,4,GL_FLOAT,GL_FALSE,16,(void*)0);}
float tw(const char*s,float ps){if(!gTex)return strlen(s)*4*ps-ps;float w=0;for(;*s;s++){int c=(unsigned char)*s;if(c>=32&&c<128)w+=gBC[c-32].xadvance;}return w*ps*7/FPX;}
void text(const char*s,float x,float y,float ps,float r,float g,float b){
 if(!gTex){btext(s,x,y,ps,r,g,b);return;}
 float sc=ps*7/FPX,by=y+5*ps;std::vector<float> v;
 for(;*s;s++){int c=(unsigned char)*s;if(c<32||c>=128)continue;stbtt_aligned_quad q;float xp=0,yp=0;stbtt_GetBakedQuad(gBC,1024,1024,c-32,&xp,&yp,&q,1);
  float x0=x+q.x0*sc,x1=x+q.x1*sc,y0=by+q.y0*sc,y1=by+q.y1*sc;
  v.insert(v.end(),{x0,y0,q.s0,q.t0,x1,y0,q.s1,q.t0,x1,y1,q.s1,q.t1,x0,y0,q.s0,q.t0,x1,y1,q.s1,q.t1,x0,y1,q.s0,q.t1});x+=xp*sc;}
 if(v.empty())return;
 glUseProgram(gTP);glUniform2f(uTS,(float)W,(float)H);glUniform4f(uTC,r,g,b,1);glActiveTexture(GL_TEXTURE0);glBindTexture(GL_TEXTURE_2D,gTex);
 glBindVertexArray(gTVao);glBindBuffer(GL_ARRAY_BUFFER,gTVbo);glBufferData(GL_ARRAY_BUFFER,v.size()*4,v.data(),GL_STREAM_DRAW);
 glDrawArrays(GL_TRIANGLES,0,(int)v.size()/4);glUseProgram(gProg);}

// Layout helpers (Blender-like proportions adapted to mobile landscape)
float headerH(){return H*.078f;}
float timelineH(){return H*.095f;}
float timelineY(){return H-timelineH();}
float outlinerW(){return showOutliner?W*.175f:0;}
float propsW(){return showProperties?W*.22f:0;}
float shelfW(){return showToolShelf?W*.068f:0;}
float viewportX(){return outlinerW()+shelfW();}
float viewportW(){return W-outlinerW()-shelfW()-propsW();}

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
 eglQuerySurface(dpy,surf,EGL_WIDTH,&W);eglQuerySurface(dpy,surf,EGL_HEIGHT,&H);scanProjects();return true;}
void termEGL(){
 if(dpy!=EGL_NO_DISPLAY){eglMakeCurrent(dpy,EGL_NO_SURFACE,EGL_NO_SURFACE,EGL_NO_CONTEXT);
  if(ctx!=EGL_NO_CONTEXT)eglDestroyContext(dpy,ctx);if(surf!=EGL_NO_SURFACE)eglDestroySurface(dpy,surf);eglTerminate(dpy);}
 dpy=EGL_NO_DISPLAY;ctx=EGL_NO_CONTEXT;surf=EGL_NO_SURFACE;}

// ---------- render helpers ----------
M gVP;int gAxis=-1,gIdx=0;bool gDrag=false;
const V AX[3]={{1,0,0},{0,1,0},{0,0,1}};
const float AC[3][3]={{.95f,.28f,.28f},{.32f,.82f,.35f},{.30f,.52f,.98f}};
float gl(){return cd*.18f;}
bool prj(V p,float&x,float&y){const float*m=gVP.m;
 float cx=m[0]*p.x+m[4]*p.y+m[8]*p.z+m[12],cy=m[1]*p.x+m[5]*p.y+m[9]*p.z+m[13],cw=m[3]*p.x+m[7]*p.y+m[11]*p.z+m[15];
 if(cw<.01f)return false;x=(cx/cw*.5f+.5f)*W;y=(1-(cy/cw*.5f+.5f))*H;return true;}
V ringPt(int a,int i){float th=i*2*PI/32,c=cosf(th)*gl()*.75f,s=sinf(th)*gl()*.75f;V o=objs[sel].cur.p;
 return a==0?o+V{0,c,s}:a==1?o+V{s,0,c}:o+V{c,s,0};}
int hitGizmo(float x,float y){
 if(sel<0||tool>2||editorMode!=OBJECT_MODE)return -1;
 V o=objs[sel].cur.p;float ox,oy;if(!prj(o,ox,oy))return -1;
 int best=-1;float bd=H*.055f;
 for(int a=0;a<3;a++){float d=1e9f;int bi=0;
  if(tool==1){for(int i=0;i<32;i++){float px,py;if(prj(ringPt(a,i),px,py)){float dd=hypotf(px-x,py-y);if(dd<d){d=dd;bi=i;}}}}
  else{float ex,ey;if(prj(o+AX[a]*gl(),ex,ey)){float vx=ex-ox,vy=ey-oy,t=std::clamp(((x-ox)*vx+(y-oy)*vy)/(vx*vx+vy*vy+1e-3f),0.f,1.f);d=hypotf(x-ox-vx*t,y-oy-vy*t);}}
  if(d<bd){bd=d;best=a;gIdx=bi;}}
 return best;}
void drawGizmo(){
 if(sel<0||tool>2)return;
 V p=objs[sel].cur.p;float L=gl(),th=L*.022f;
 auto box=[&](V c,V sc,const float*k){T t;t.p=c;t.s=sc;M m=model(t);draw(meshes[0],mul(gVP,m),m,k[0],k[1],k[2],1,0);};
 static const float Y[3]={1.f,.92f,.25f};
 for(int a=0;a<3;a++){const float*k=(gDrag&&a==gAxis)?Y:AC[a];
  if(tool==1){for(int i=0;i<32;i++)box(ringPt(a,i),V{th*2.2f,th*2.2f,th*2.2f},k);}
  else{V sc{th,th,th};(&sc.x)[a]=L;box(p+AX[a]*(L*.5f),sc,k);float e=th*(tool==2?6.5f:3.8f);box(p+AX[a]*L,V{e,e,e},k);}}}

// Bone drawing (Blender-style octahedral-ish sticks)
void drawBones(){
 if(rigs.empty())return;
 for(size_t ri=0;ri<rigs.size();ri++){
  auto&arm=rigs[ri];if(!arm.visible)continue;
  for(size_t bi=0;bi<arm.bones.size();bi++){
   auto&b=arm.bones[bi];
   V a=b.head,c=b.tail;
   if(editorMode==POSE_MODE){ // simple pose offset
    a=a+b.pose.p;c=c+b.pose.p;
   }
   float ax,ay,cx,cy;
   if(!prj(a,ax,ay)||!prj(c,cx,cy))continue;
   float dx=cx-ax,dy=cy-ay,L=hypotf(dx,dy);
   bool selected=(ri==(size_t)selRig&&bi==(size_t)selBone);
   float r=selected?.98f:.78f,g=selected|.55f:.42f,bl=selected?.18f:.12f;
   // shaft
   float thick=selected?4.5f:3.2f;
   // simple thick line via rects along direction
   int steps=std::max(4,(int)(L/6));
   for(int s=0;s<steps;s++){
    float t0=(float)s/steps,t1=(float)(s+1)/steps;
    float x0=ax+dx*t0,y0=ay+dy*t0;
    rect(x0-thick*.5f,y0-thick*.5f,thick,thick,r,g,bl,1,2);
   }
   // head sphere
   float hr=selected?H*.014f:H*.011f;
   rect(ax-hr,ay-hr,hr*2,hr*2,r,g,bl,1,hr);
   // tail
   float tr=selected?H*.010f:H*.008f;
   rect(cx-tr,cy-tr,tr*2,tr*2,.95f,.7f,.25f,1,tr);
  }
 }}

// Navigation gizmo (Blender View3D)
struct ND{float x,y,z;int a;bool pos;};
float navR(){return H*.10f;} float navX(){return W-propsW()-navR()-14;} float navY(){return headerH()+navR()+18;}
void navPts(ND*d){V f=norm(tgt-camEye()),s=norm(cross(f,V{0,1,0})),u=cross(s,f);float R=navR();
 for(int i=0;i<6;i++){int a=i%3;V v=AX[a]*(i<3?1.f:-1.f);d[i]={navX()+dot(v,s)*R*.70f,navY()-dot(v,u)*R*.70f,dot(v,f),a,i<3};}}
void drawNav(){ND d[6];navPts(d);float R=navR(),cx=navX(),cy=navY();
 rect(cx-R-5,cy-R-5,2*R+10,2*R+10,.04f,.045f,.055f,.55f,R+5);
 std::sort(d,d+6,[](const ND&p,const ND&q){return p.z>q.z;});
 static const char*LB[3]={"X","Y","Z"};
 for(auto&e:d){const float*c=AC[e.a];float k=e.pos?1.f:.48f,r=e.pos?H*.022f:H*.015f;
  if(e.pos)for(int j=1;j<5;j++)rect(cx+(e.x-cx)*j/5-1.5f,cy+(e.y-cy)*j/5-1.5f,3,3,c[0],c[1],c[2],.9f,1);
  rect(e.x-r,e.y-r,2*r,2*r,c[0]*k,c[1]*k,c[2]*k,1,r);
  if(e.pos){float ps=H*.005f;text(LB[e.a],e.x-tw(LB[e.a],ps)/2,e.y-2.2f*ps,ps,1,1,1);}}}

// ---------- HOME SCREEN (Blender splash style) ----------
void drawHome(){
 glDisable(GL_DEPTH_TEST);glClearColor(.07f,.075f,.085f,1);glClear(GL_COLOR_BUFFER_BIT);
 float m=W*.04f,top=H*.06f;
 // title
 text("NOMAD ANIMATOR",m,top,H*.026f,.93f,.93f,.96f);
 text("3D Animation  ·  Mobile",m,top+H*.034f,H*.011f,.45f,.50f,.58f);

 // New Project card
 float cw=W*.24f,ch=H*.32f,cy=H*.20f;
 rect(m,cy,cw,ch,.11f,.12f,.145f,1,18);
 rectBorder(m,cy,cw,ch,.22f,.25f,.30f,1.5f);
 text("+",m+cw*.40f,cy+ch*.22f,H*.055f,.55f,.60f,.68f);
 text("New Project",m+cw*.18f,cy+ch*.62f,H*.013f,.92f,.93f,.95f);
 text("Blank scene",m+cw*.22f,cy+ch*.78f,H*.009f,.48f,.52f,.58f);

 // Recent
 float rx=m+cw+16,rw=W-m*2-cw-16;
 rect(rx,cy,rw,ch,.09f,.095f,.11f,1,16);
 text("Recent Projects",rx+18,cy+16,H*.012f,.78f,.80f,.85f);
 float ry=cy+H*.065f;
 for(size_t i=0;i<recentProjects.size()&&i<5;i++){
  bool hi=(int)i==browserSel;
  rect(rx+12,ry-4,rw-24,H*.038f,hi?.16f:.10f,hi|.12f:.11f,hi|.14f:.13f,1,8);
  text(recentProjects[i].c_str(),rx+22,ry,H*.011f,.95f,.95f,.97f);
  ry+=H*.045f;}
 if(recentProjects.empty())text("No .MAD projects yet",rx+22,ry,H*.010f,.40f,.44f,.50f);

 // Bottom action buttons
 float by=cy+ch+20,bw0=(W-2*m-40)/4.f;
 const char*bs[]={"Open .MAD","Import glTF","Export glTF","Continue"};
 for(int i=0;i<4;i++){
  rect(m+i*(bw0+10),by,bw0,H*.078f,.13f,.14f,.17f,1,12);
  text(bs[i],m+i*(bw0+10)+bw0*.12f,by+H*.028f,H*.011f,.92f,.93f,.95f);}
 text(projectStatus.c_str(),m,by+H*.10f,H*.009f,.42f,.46f,.52f);
 text("Files are stored in app data folder",m,H-H*.04f,H*.008f,.35f,.38f,.42f);
}

// ---------- FILE BROWSER ----------
void drawFileBrowser(){
 glDisable(GL_DEPTH_TEST);glClearColor(.06f,.065f,.075f,1);glClear(GL_COLOR_BUFFER_BIT);
 float m=W*.05f;
 const char*titles[]={"Open .MAD Project","Import glTF Rig","Save As"};
 text(titles[fileBrowserMode],m,H*.06f,H*.020f,.92f,.93f,.96f);
 text("Select a file from app storage",m,H*.10f,H*.010f,.48f,.52f,.58f);

 float listY=H*.16f,listH=H*.55f;
 rect(m,listY,W-2*m,listH,.09f,.095f,.11f,1,12);
 float yy=listY+16;
 if(browserFiles.empty())text("No matching files found",m+20,yy+20,H*.012f,.45f,.48f,.52f);
 for(size_t i=0;i<browserFiles.size()&&i<10;i++){
  bool hi=(int)i==browserSel;
  rect(m+10,yy,W-2*m-20,H*.048f,hi?.20f:.11f,hi|.15f:.12f,hi|.18f:.14f,1,8);
  text(browserFiles[i].c_str(),m+24,yy+H*.014f,H*.012f,1,1,1);
  yy+=H*.055f;}

 float by=listY+listH+18,bw0=(W-2*m-20)/2.f;
 rect(m,by,bw0,H*.075f,.14f,.16f,.20f,1,12);text("Cancel",m+bw0*.32f,by+H*.025f,H*.013f,.9f,.9f,.92f);
 rect(m+bw0+20,by,bw0,H*.075f,.22f,.45f,.28f,1,12);text("Open",m+bw0+20+bw0*.36f,by+H*.025f,H*.013f,1,1,1);
}

// ---------- EDITOR UI (Blender layout) ----------
void drawEditorHeader(){
 float h=headerH();
 // dark top bar like Blender
 rect(0,0,W,h,.055f,.058f,.068f,1,0);
 // logo / app name
 rect(8,6,W*.11f,h-12,.10f,.11f,.13f,1,7);
 text("Nomad",16,h*.30f,H*.011f,.92f,.93f,.95f);

 // Mode selector (Object / Edit / Pose) - Blender style
 float bx=W*.13f;
 const char*md[]={"Object","Edit","Pose"};
 for(int i=0;i<3;i++){
  bool on=i==(int)editorMode;
  rect(bx+i*W*.09f,7,W*.082f,h-14,on?.22f:.09f,on?.18f:.10f,on|.14f:.12f,1,7);
  text(md[i],bx+10+i*W*.09f,h*.30f,H*.010f,on?.98f:.78f,on?.98f:.80f,on?.98f:.84f);
 }

 // Right actions
 float px=W*.42f;
 const char*actions[]={"Save","glTF","Out","Props","Shelf"};
 for(int i=0;i<5;i++){
  float ww=W*.065f;
  bool on=(i==2&&showOutliner)||(i==3&&showProperties)||(i==4&&showToolShelf);
  rect(px+i*(ww+6),7,ww,h-14,on?.16f:.09f,.11f,.13f,1,7);
  text(actions[i],px+8+i*(ww+6),h*.30f,H*.009f,.85f,.87f,.90f);
 }
}

void drawToolShelf(){
 if(!showToolShelf)return;
 float x=outlinerW(),w=shelfW(),y0=headerH(),h=timelineY()-headerH();
 rect(x,y0,w,h,.07f,.075f,.085f,1,0);
 // tools depend on mode
 const char* labels[8];int n=0;
 if(editorMode==OBJECT_MODE){
  labels[0]="+";labels[1]="Rig";labels[2]="G";labels[3]="R";labels[4]="S";labels[5]="Cam";labels[6]="Key";labels[7]="Play";n=8;
 }else if(editorMode==EDIT_MODE){
  labels[0]="Bone";labels[1]="G";labels[2]="Del";labels[3]="";n=3;
 }else{ // POSE
  labels[0]="G";labels[1]="R";labels[2]="Reset";labels[3]="";n=3;
 }
 float bh0=H*.058f,gap=H*.012f;
 for(int i=0;i<n;i++){
  if(!labels[i][0])continue;
  float yy=y0+12+i*(bh0+gap);
  bool on=false;
  if(editorMode==OBJECT_MODE){
   if(i==2&&tool==0)on=true;if(i==3&&tool==1)on=true;if(i==4&&tool==2)on=true;if(i==5&&tool==3)on=true;
  }else if(editorMode==EDIT_MODE){if(i==1&&tool==0)on=true;}
  else{if(i==0&&tool==0)on=true;if(i==1&&tool==1)on=true;}
  rect(x+6,yy,w-12,bh0,on?.25f:.10f,on|.18f:.11f,on|.14f:.13f,1,9);
  float ps=H*.012f;
  text(labels[i],x+(w-tw(labels[i],ps))/2,yy+bh0*.28f,ps,1,1,1);
 }
}

void drawOutliner(){
 if(!showOutliner)return;
 float w=outlinerW(),y0=headerH(),h=timelineY()-headerH();
 rect(0,y0,w,h,.065f,.07f,.08f,1,0);
 text("Outliner",10,y0+10,H*.010f,.72f,.75f,.80f);
 float yy=y0+H*.045f;
 // Scene collection
 text("Scene",12,yy,H*.009f,.55f,.58f,.62f);yy+=H*.032f;
 for(int i=0;i<(int)objs.size();++i){
  bool a=i==sel&&editorMode==OBJECT_MODE;
  rect(6,yy-3,w-12,H*.034f,a?.20f:.08f,a?.14f:.09f,a|.12f:.10f,1,6);
  text(objs[i].name.c_str(),16,yy,H*.009f,a?.98f:.88f,a?.98f:.88f,a?.98f:.90f);
  yy+=H*.038f;}
 for(size_t ri=0;ri<rigs.size();ri++){
  bool aRig=(int)ri==selRig;
  rect(6,yy-3,w-12,H*.034f,aRig?.18f:.08f,aRig|.13f:.09f,aRig|.16f:.10f,1,6);
  text(rigs[ri].name.c_str(),16,yy,H*.009f,.75f,.82f,.95f);
  yy+=H*.038f;
  if(aRig||editorMode!=OBJECT_MODE){
   for(size_t bi=0;bi<rigs[ri].bones.size();bi++){
    bool aB=(int)ri==selRig&&(int)bi==selBone;
    rect(14,yy-2,w-22,H*.030f,aB?.22f:.07f,aB|.16f:.08f,aB|.12f:.09f,1,5);
    text(rigs[ri].bones[bi].name.c_str(),22,yy,H*.0085f,aB?.98f:.70f,aB?.90f:.72f,aB?.70f:.78f);
    yy+=H*.034f;
   }
  }
 }
}

void drawProperties(){
 if(!showProperties)return;
 float x=W-propsW(),w=propsW(),y0=headerH(),h=timelineY()-headerH();
 rect(x,y0,w,h,.06f,.065f,.075f,1,0);
 text("Properties",x+12,y0+10,H*.010f,.72f,.75f,.80f);

 const char*modeName=editorMode==POSE_MODE?"Pose Mode":editorMode==EDIT_MODE?"Edit Mode":"Object Mode";
 text(modeName,x+12,y0+H*.045f,H*.011f,.95f,.70f,.35f);

 float yy=y0+H*.09f;
 char buf[80];
 if(editorMode==OBJECT_MODE&&sel>=0&&sel<(int)objs.size()){
  Obj&o=objs[sel];
  text(o.name.c_str(),x+12,yy,H*.011f,.90f,.92f,.95f);yy+=H*.040f;
  text("Location",x+12,yy,H*.009f,.55f,.58f,.62f);yy+=H*.028f;
  snprintf(buf,80,"X  %.3f",o.cur.p.x);text(buf,x+16,yy,H*.009f,.78f,.80f,.84f);yy+=H*.030f;
  snprintf(buf,80,"Y  %.3f",o.cur.p.y);text(buf,x+16,yy,H*.009f,.78f,.80f,.84f);yy+=H*.030f;
  snprintf(buf,80,"Z  %.3f",o.cur.p.z);text(buf,x+16,yy,H*.009f,.78f,.80f,.84f);yy+=H*.038f;
  text("Rotation",x+12,yy,H*.009f,.55f,.58f,.62f);yy+=H*.028f;
  snprintf(buf,80,"X  %.2f",o.cur.r.x*57.3f);text(buf,x+16,yy,H*.009f,.78f,.80f,.84f);yy+=H*.030f;
  snprintf(buf,80,"Y  %.2f",o.cur.r.y*57.3f);text(buf,x+16,yy,H*.009f,.78f,.80f,.84f);yy+=H*.030f;
  snprintf(buf,80,"Z  %.2f",o.cur.r.z*57.3f);text(buf,x+16,yy,H*.009f,.78f,.80f,.84f);yy+=H*.038f;
  text("Scale",x+12,yy,H*.009f,.55f,.58f,.62f);yy+=H*.028f;
  snprintf(buf,80,"%.3f  %.3f  %.3f",o.cur.s.x,o.cur.s.y,o.cur.s.z);text(buf,x+16,yy,H*.009f,.78f,.80f,.84f);
 }else if((editorMode==EDIT_MODE||editorMode==POSE_MODE)&&selRig>=0&&selBone>=0){
  auto&b=rigs[selRig].bones[selBone];
  text(b.name.c_str(),x+12,yy,H*.011f,.90f,.85f,.55f);yy+=H*.040f;
  text("Head",x+12,yy,H*.009f,.55f,.58f,.62f);yy+=H*.028f;
  snprintf(buf,80,"%.2f  %.2f  %.2f",b.head.x,b.head.y,b.head.z);text(buf,x+16,yy,H*.009f,.78f,.80f,.84f);yy+=H*.032f;
  text("Tail",x+12,yy,H*.009f,.55f,.58f,.62f);yy+=H*.028f;
  snprintf(buf,80,"%.2f  %.2f  %.2f",b.tail.x,b.tail.y,b.tail.z);text(buf,x+16,yy,H*.009f,.78f,.80f,.84f);yy+=H*.032f;
  snprintf(buf,80,"Parent: %d",b.parent);text(buf,x+12,yy,H*.009f,.65f,.68f,.72f);
 }else{
  text("No selection",x+12,yy,H*.010f,.50f,.53f,.58f);
 }
}

void drawTimeline(){
 float y=timelineY(),h=timelineH();
 float x0=outlinerW(),w=W-outlinerW()-propsW();
 rect(x0,y,w,h,.05f,.055f,.065f,1,0);
 // top separator line
 rect(x0,y,w,1.5f,.18f,.20f,.24f,1,0);

 text("Timeline",x0+10,y+6,H*.009f,.65f,.68f,.72f);
 // frame numbers
 float p2=h*.09f;
 for(int f=0;f<=(int)(DUR*24);f+=6){
  float x=x0+14+(f/(DUR*24.f))*(w-28);
  rect(x-1,y+h*.42f,2,h*.16f,.32f,.34f,.38f);
  if(f%24==0){char b[8];snprintf(b,8,"%d",f/24);text(b,x-6,y+h*.12f,p2,.60f,.62f,.66f);}
 }
 // keys
 if(sel>=0)for(auto&k:objs[sel].k){
  float x=x0+14+(k.t/DUR)*(w-28);
  rect(x-5,y+h*.62f,10,10,.95f,.72f,.18f,1,2);}
 // playhead
 float x=x0+14+(tm/DUR)*(w-28);
 rect(x-2,y+3,4,h-6,.95f,.28f,.22f,1,2);
 // play button indicator
 if(playing)text("PLAYING",x0+w-70,y+6,H*.008f,.95f,.55f,.25f);
}

void frame(){
 if(screen==HOME){drawHome();eglSwapBuffers(dpy,surf);return;}
 if(screen==FILE_BROWSER){drawFileBrowser();eglSwapBuffers(dpy,surf);return;}

 // 3D viewport
 glViewport(0,0,W,H);
 glClearColor(.16f,.17f,.20f,1); // Blender-ish viewport gray
 glClear(GL_COLOR_BUFFER_BIT|GL_DEPTH_BUFFER_BIT);
 glEnable(GL_DEPTH_TEST);
 gVP=mul(persp(FOV,(float)W/H,.1f,100),lookAt(camEye(),tgt,{0,1,0}));
 // grid
 draw(meshes[4],gVP,id(),.32f,.33f,.36f,1,0);
 // objects
 for(int i=0;i<(int)objs.size();i++){
  Obj&o=objs[i];M mod=model(o.cur);
  float hlt=(i==sel&&editorMode==OBJECT_MODE)?.28f:0;
  draw(meshes[o.mesh],mul(gVP,mod),mod,o.col.x+(1-o.col.x)*hlt,o.col.y+(1-o.col.y)*hlt,o.col.z+(1-o.col.z)*hlt,1,1);
 }
 glDisable(GL_DEPTH_TEST);
 if(sel>=0&&tool<3&&editorMode==OBJECT_MODE)drawGizmo();
 drawBones();

 // UI overlays
 drawEditorHeader();
 drawToolShelf();
 drawOutliner();
 drawProperties();
 drawTimeline();
 drawNav();

 // status bar (bottom of timeline area already used; small floating status)
 if(!projectStatus.empty()){
  float ps=H*.008f;
  text(projectStatus.c_str(),viewportX()+8,timelineY()-ps*3.5f,ps,.55f,.58f,.62f);
 }
 eglSwapBuffers(dpy,surf);}

// ---------- input ----------
void pressTool(int i){
 if(editorMode==OBJECT_MODE){
  if(i==0){addObj(0);return;}
  if(i==1){addRig();return;}
  if(i==2||i==3||i==4){tool=i-2;return;}
  if(i==5){tool=3;return;}
  if(i==6&&sel>=0){
   Obj&o=objs[sel];bool f=false;
   for(auto&k:o.k)if(fabsf(k.t-tm)<.04f){k.x=o.cur;f=true;}
   if(!f){o.k.push_back({tm,o.cur});std::sort(o.k.begin(),o.k.end(),[](const Key&a,const Key&b){return a.t<b.t;});}
   projectStatus="Keyframe inserted";return;}
  if(i==7){playing=!playing;return;}
 }else if(editorMode==EDIT_MODE){
  if(i==0){addBone();return;}
  if(i==1){tool=0;return;}
  if(i==2){deleteSelected();return;}
 }else if(editorMode==POSE_MODE){
  if(i==0){tool=0;return;}
  if(i==1){tool=1;return;}
  if(i==2&&selRig>=0&&selBone>=0){rigs[selRig].bones[selBone].pose={};projectStatus="Pose reset";return;}
 }
}
void scrub(float x){
 float x0=outlinerW(),x1=W-propsW();
 tm=roundf(std::clamp((x-x0-14)/(x1-x0-28),0.f,1.f)*DUR*24)/24.f;applyAnim();}
void pick(float x,float y){
 // first try bones if in edit/pose
 if(editorMode!=OBJECT_MODE&&!rigs.empty()){
  float bestD=H*.04f;int bestR=-1,bestB=-1;
  for(size_t ri=0;ri<rigs.size();ri++){
   auto&arm=rigs[ri];if(!arm.visible)continue;
   for(size_t bi=0;bi<arm.bones.size();bi++){
    float ax,ay,cx,cy;
    V a=arm.bones[bi].head,c=arm.bones[bi].tail;
    if(editorMode==POSE_MODE){a=a+arm.bones[bi].pose.p;c=c+arm.bones[bi].pose.p;}
    if(!prj(a,ax,ay)||!prj(c,cx,cy))continue;
    // distance to segment
    float dx=cx-ax,dy=cy-ay,l2=dx*dx+dy*dy+1e-5f;
    float t=std::clamp(((x-ax)*dx+(y-ay)*dy)/l2,0.f,1.f);
    float d=hypotf(x-ax-dx*t,y-ay-dy*t);
    if(d<bestD){bestD=d;bestR=(int)ri;bestB=(int)bi;}
   }
  }
  if(bestR>=0){selRig=bestR;selBone=bestB;sel=-1;return;}
 }
 // objects
 V e=camEye(),f=norm(tgt-e),s=norm(cross(f,V{0,1,0})),u=cross(s,f);
 float th=tanf(FOV/2),as=(float)W/H;V d=norm(f+s*((2*x/W-1)*th*as)+u*((1-2*y/H)*th));
 static const float RF[3]={.87f,.5f,1.42f};int best=-1;float bt=1e9f;
 for(int i=0;i<(int)objs.size();i++){T&t=objs[i].cur;float r=RF[objs[i].mesh]*std::max({t.s.x,t.s.y,t.s.z});
  V oc=e-t.p;float b=dot(oc,d),c=dot(oc,oc)-r*r,ds=b*b-c;if(ds<0)continue;
  float tt=-b-sqrtf(ds);if(tt>0&&tt<bt){bt=tt;best=i;}}
 sel=best;if(best>=0){selBone=-1;}
}
void orbit(float dx,float dy){yaw-=dx*.0055f;pitch=std::clamp(pitch+dy*.0055f,-1.48f,1.48f);}
void gdrag(float dx,float dy){
 if(sel<0)return;
 T&t=objs[sel].cur;V o=t.p;float ox,oy,ex,ey;
 if(tool==1){float px,py,qx,qy;if(!prj(ringPt(gAxis,gIdx+1),px,py)||!prj(ringPt(gAxis,gIdx+31),qx,qy))return;
  float vx=px-qx,vy=py-qy,l=hypotf(vx,vy);if(l<1)return;(&t.r.x)[gAxis]+=(dx*vx+dy*vy)/l*.011f;return;}
 if(!prj(o,ox,oy)||!prj(o+AX[gAxis]*gl(),ex,ey))return;
 float vx=ex-ox,vy=ey-oy,k=(dx*vx+dy*vy)/(vx*vx+vy*vy+1e-3f);
 if(tool==0)t.p=t.p+AX[gAxis]*(k*gl());else{float&sc=(&t.s.x)[gAxis];sc=std::max(.05f,sc*(1+k));}}
void snap(float x,float y){ND d[6];navPts(d);
 for(auto&e:d)if(hypotf(x-e.x,y-e.y)<H*.032f){
  if(e.a==0){yaw=e.pos?PI/2:-PI/2;pitch=0;}else if(e.a==1)pitch=e.pos?1.42f:-1.42f;else{yaw=e.pos?0.f:PI;pitch=0;}return;}}

int32_t onInput(android_app*,AInputEvent*e){
 static int mode=0;static float lx,ly,sx,sy,pinch;static bool moved,rl;
 if(AInputEvent_getType(e)!=AINPUT_EVENT_TYPE_MOTION)return 0;
 int act=AMotionEvent_getAction(e)&AMOTION_EVENT_ACTION_MASK,n=(int)AMotionEvent_getPointerCount(e);
 float x=AMotionEvent_getX(e,0),y=AMotionEvent_getY(e,0);

 if(screen==HOME){
  if(act==AMOTION_EVENT_ACTION_UP){
   float m=W*.04f,cw=W*.24f,ch=H*.32f,cy=H*.20f,by=cy+ch+20,bw0=(W-2*m-40)/4.f;
   // New
   if(x>=m&&x<=m+cw&&y>=cy&&y<=cy+ch){projectName="Untitled Project";newProject();screen=EDITOR;}
   // Recent click
   else if(x>=m+cw+16&&y>=cy+H*.06f&&y<=cy+ch-10&&!recentProjects.empty()){
    int ri=(int)((y-(cy+H*.065f))/(H*.045f));
    if(ri>=0&&ri<(int)recentProjects.size())loadMAD(recentProjects[ri]);
   }
   // buttons
   else if(y>=by&&y<=by+H*.078f){
    int bi=(int)((x-m)/(bw0+10));
    if(bi==0){fileBrowserMode=0;scanBrowser(".mad");screen=FILE_BROWSER;}
    else if(bi==1){fileBrowserMode=1;scanBrowser(".gltf");screen=FILE_BROWSER;}
    else if(bi==2){exportGLTF();}
    else if(bi==3){screen=EDITOR;}
   }
  }return 1;
 }

 if(screen==FILE_BROWSER){
  if(act==AMOTION_EVENT_ACTION_UP){
   float m=W*.05f,listY=H*.16f,listH=H*.55f,by=listY+listH+18,bw0=(W-2*m-20)/2.f;
   // list select
   if(y>=listY&&y<=listY+listH){
    int ri=(int)((y-listY-16)/(H*.055f));
    if(ri>=0&&ri<(int)browserFiles.size())browserSel=ri;
   }
   // Cancel
   else if(y>=by&&y<=by+H*.075f&&x>=m&&x<m+bw0){screen=HOME;browserSel=-1;}
   // Open
   else if(y>=by&&y<=by+H*.075f&&x>=m+bw0+20){
    if(browserSel>=0&&browserSel<(int)browserFiles.size()){
     if(fileBrowserMode==0){loadMAD(browserFiles[browserSel].substr(0,browserFiles[browserSel].size()-4));}
     else if(fileBrowserMode==1){importGLTF(browserFiles[browserSel]);}
    }else projectStatus="Select a file first";
   }
  }return 1;
 }

 // EDITOR
 if(act==AMOTION_EVENT_ACTION_DOWN){
  moved=false;rl=true;sx=x;sy=y;pinch=0;gDrag=false;
  // Header
  if(y<headerH()+4){
   float bx=W*.13f;
   if(x>=bx&&x<bx+W*.27f){int md=(int)((x-bx)/(W*.09f));if(md>=0&&md<=2)editorMode=(EditorMode)md;}
   else{
    float px=W*.42f,ww=W*.065f;int a=(int)((x-px)/(ww+6));
    if(x>=px){
     if(a==0)saveMAD();
     else if(a==1)exportGLTF();
     else if(a==2)showOutliner=!showOutliner;
     else if(a==3)showProperties=!showProperties;
     else if(a==4)showToolShelf=!showToolShelf;
    }
   }mode=2;
  }
  // Timeline
  else if(y>timelineY()){mode=3;scrub(x);}
  // Nav gizmo
  else if(hypotf(x-navX(),y-navY())<navR()+10)mode=4;
  // Tool shelf
  else if(showToolShelf&&x>=outlinerW()&&x<outlinerW()+shelfW()&&y>headerH()&&y<timelineY()){
   float y0=headerH()+12,bh0=H*.058f,gap=H*.012f;
   int idx=(int)((y-y0)/(bh0+gap));
   pressTool(idx);mode=2;
  }
  // Outliner click
  else if(showOutliner&&x<outlinerW()&&y>headerH()&&y<timelineY()){
   // simple selection by y order (approximate)
   float yy=headerH()+H*.045f+H*.032f;
   for(int i=0;i<(int)objs.size();i++){
    if(y>=yy-3&&y<=yy+H*.034f){sel=i;selBone=-1;editorMode=OBJECT_MODE;break;}
    yy+=H*.038f;}
   for(size_t ri=0;ri<rigs.size();ri++){
    if(y>=yy-3&&y<=yy+H*.034f){selRig=(int)ri;sel=-1;break;}
    yy+=H*.038f;
    if((int)ri==selRig||editorMode!=OBJECT_MODE){
     for(size_t bi=0;bi<rigs[ri].bones.size();bi++){
      if(y>=yy-2&&y<=yy+H*.030f){selRig=(int)ri;selBone=(int)bi;sel=-1;break;}
      yy+=H*.034f;}
    }
   }
   mode=2;
  }
  else{
   int a=hitGizmo(x,y);
   if(a>=0){gAxis=a;gDrag=true;mode=5;}
   else mode=1;
  }
 }else if(act==AMOTION_EVENT_ACTION_POINTER_DOWN){moved=true;rl=true;pinch=0;}
 else if(act==AMOTION_EVENT_ACTION_POINTER_UP){rl=true;pinch=0;}
 else if(act==AMOTION_EVENT_ACTION_MOVE){
  if(mode==3)scrub(x);
  else if(mode==1&&n>=2){float d=hypotf(AMotionEvent_getX(e,1)-x,AMotionEvent_getY(e,1)-y);
   if(pinch>0&&d>1)cd=std::clamp(cd*pinch/d,2.f,45.f);pinch=d;moved=true;}
  else if(mode==1||mode==4||mode==5){
   if(rl){rl=false;lx=x;ly=y;}
   else{float dx=x-lx,dy=y-ly;lx=x;ly=y;if(hypotf(x-sx,y-sy)>18)moved=true;
    if(mode==5)gdrag(dx,dy);else if(moved)orbit(dx,dy);}}
 }else if(act==AMOTION_EVENT_ACTION_UP||act==AMOTION_EVENT_ACTION_CANCEL){
  if(mode==1&&!moved)pick(x,y);
  if(mode==4&&!moved)snap(x,y);
  mode=0;gDrag=false;}
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
