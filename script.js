(() => {
  /* ========== DOM ========== */
  const svg = document.getElementById('graphSvg');
  const regexInput = document.getElementById('regexInput');
  const stringInput = document.getElementById('stringInput');
  const buildBtn = document.getElementById('buildBtn');
  const resetBtn = document.getElementById('resetBtn');
  const convertBtn = document.getElementById('convertBtn');
  const simulateNfaBtn = document.getElementById('simulateNfaBtn');
  const simulateDfaBtn = document.getElementById('simulateDfaBtn');
  const stepDescription = document.getElementById('stepDescription');
  const concatView = document.getElementById('concatView');
  const postfixView = document.getElementById('postfixView');
  const resultView = document.getElementById('resultView');
  const regexPanel = document.getElementById('regexPanel');
  const pdaPanel = document.getElementById('pdaPanel');
  const regexGuide = document.getElementById('regexGuide');
  const pdaGuide = document.getElementById('pdaGuide');
  const langInput = document.getElementById('langInput');
  const constraintInput = document.getElementById('constraintInput');
  const wordPattern = document.getElementById('wordPattern');
  const buildPdaBtn = document.getElementById('buildPdaBtn');
  const resetPdaBtn = document.getElementById('resetPdaBtn');
  const pdaStringInput = document.getElementById('pdaStringInput');
  const simulatePdaBtn = document.getElementById('simulatePdaBtn');
  const langDescView = document.getElementById('langDescView');
  const initStackView = document.getElementById('initStackView');
  const pdaResultView = document.getElementById('pdaResultView');
  const pdaDescription = document.getElementById('pdaDescription');
  const pdaTableSection = document.getElementById('pdaTransitionTableSection');
  const pdaTraceSection = document.getElementById('pdaSimTraceSection');
  const nfaTableSection = document.getElementById('nfaTransitionTableSection');
  const exponentInputs = document.getElementById('exponentInputs');
  const wordInputs = document.getElementById('wordInputs');

  const SVG_NS = 'http://www.w3.org/2000/svg';
  const VIEW_W = 1200, VIEW_H = 700, RADIUS = 26;
  const START_COLOR = '#16a34a', ACCEPT_COLOR = '#dc2626', NORMAL_COLOR = '#2563eb', EDGE_COLOR = '#64748b';

  let stateCounter = 0, edgeCounter = 0;
  let builtNfa = null, builtDfa = null, builtPda = null;
  let currentMode = 'epsilon-nfa';

  function resetIds() { stateCounter = 0; edgeCounter = 0; }
  function newStateId(p) { return `${p||'q'}${stateCounter++}`; }
  function newEdgeId(p) { return `${p||'e'}${edgeCounter++}`; }
  function isOperand(ch) { return /^[a-zA-Z0-9]$/.test(ch) || ch === 'ε'; }
  function showResult(el, t, c) { el.textContent = t; el.className = c; }
  function cloneTransitions(tr) { const o = {}; for (const s in tr) o[s] = tr[s].map(e => ({...e})); return o; }
  function cloneMachine(m) {
    return { type:m.type,start:m.start,accept:Array.isArray(m.accept)?[...m.accept]:m.accept,
      states:new Set([...m.states]),transitions:cloneTransitions(m.transitions),
      __highlightStates:[],__highlightEdges:[],__sourceSets:m.__sourceSets?{...m.__sourceSets}:{} };
  }

  function seedRandom(s){let t=(s|0)+0x6D2B79F5;return()=>{t=Math.imul(t^(t>>>15),t|1);t^=t+Math.imul(t^(t>>>7),t|61);return((t^(t>>>14))>>>0)/4294967296;};}
  function hashStr(s){let h=0;for(let i=0;i<s.length;i++){h=((h<<5)-h)+s.charCodeAt(i);h|=0;}return Math.abs(h);}

  /* ========== Regex Parsing (| = union, + = Kleene plus) ========== */
  function insertConcatOperators(regex) {
    let r='', c=regex.replace(/\s+/g,'');
    for(let i=0;i<c.length;i++){
      r+=c[i];
      if(i<c.length-1){const a=c[i],b=c[i+1];
        if((isOperand(a)||a===')'||a==='*'||a==='+'||a==='?')&&(isOperand(b)||b==='(')) r+='.';}
    } return r;
  }
  function regexToPostfix(regex) {
    const out=[],st=[],prec={'|':1,'.':2,'?':3,'+':3,'*':3},ra={'*':true,'+':true,'?':true};
    for(const t of regex){
      if(isOperand(t)) out.push(t);
      else if(t==='(') st.push(t);
      else if(t===')'){while(st.length&&st[st.length-1]!=='(')out.push(st.pop());if(!st.length)throw new Error('Mismatched parentheses');st.pop();}
      else if(t in prec){while(st.length){const top=st[st.length-1];if(!(top in prec))break;if((ra[t]&&prec[top]>prec[t])||(!ra[t]&&prec[top]>=prec[t]))out.push(st.pop());else break;}st.push(t);}
      else throw new Error(`Unsupported character: ${t}`);
    }
    while(st.length){const top=st.pop();if(top==='('||top===')')throw new Error('Mismatched parentheses');out.push(top);}
    return out.join('');
  }

  /* ========== Thompson's Construction (for Epsilon-NFA) ========== */
  function createSymbolNFA(sym){const s=newStateId('q'),a=newStateId('q');return{type:'NFA',start:s,accept:a,states:new Set([s,a]),transitions:{[s]:[{id:newEdgeId('e'),symbol:sym,to:a}],[a]:[]},__highlightStates:[],__highlightEdges:[]};}
  function mergeTransitions(a,b){const o=cloneTransitions(a);for(const s in b)o[s]=(o[s]||[]).concat(b[s].map(e=>({...e})));return o;}
  function concatNFA(a,b){const t=mergeTransitions(a.transitions,b.transitions);t[a.accept]=t[a.accept]||[];t[a.accept].push({id:newEdgeId('e'),symbol:'ε',to:b.start});return{type:'NFA',start:a.start,accept:b.accept,states:new Set([...a.states,...b.states]),transitions:t,__highlightStates:[],__highlightEdges:[]};}
  function unionNFA(a,b){const s=newStateId('q'),ac=newStateId('q'),t=mergeTransitions(a.transitions,b.transitions);t[s]=[{id:newEdgeId('e'),symbol:'ε',to:a.start},{id:newEdgeId('e'),symbol:'ε',to:b.start}];t[a.accept]=t[a.accept]||[];t[b.accept]=t[b.accept]||[];t[a.accept].push({id:newEdgeId('e'),symbol:'ε',to:ac});t[b.accept].push({id:newEdgeId('e'),symbol:'ε',to:ac});t[ac]=t[ac]||[];return{type:'NFA',start:s,accept:ac,states:new Set([...a.states,...b.states,s,ac]),transitions:t,__highlightStates:[],__highlightEdges:[]};}
  function starNFA(a){const s=newStateId('q'),ac=newStateId('q'),t=cloneTransitions(a.transitions);t[s]=[{id:newEdgeId('e'),symbol:'ε',to:a.start},{id:newEdgeId('e'),symbol:'ε',to:ac}];t[a.accept]=t[a.accept]||[];t[a.accept].push({id:newEdgeId('e'),symbol:'ε',to:a.start});t[a.accept].push({id:newEdgeId('e'),symbol:'ε',to:ac});t[ac]=t[ac]||[];return{type:'NFA',start:s,accept:ac,states:new Set([...a.states,s,ac]),transitions:t,__highlightStates:[],__highlightEdges:[]};}
  function plusNFA(a){const s=newStateId('q'),ac=newStateId('q'),t=cloneTransitions(a.transitions);t[s]=[{id:newEdgeId('e'),symbol:'ε',to:a.start}];t[a.accept]=t[a.accept]||[];t[a.accept].push({id:newEdgeId('e'),symbol:'ε',to:a.start});t[a.accept].push({id:newEdgeId('e'),symbol:'ε',to:ac});t[ac]=t[ac]||[];return{type:'NFA',start:s,accept:ac,states:new Set([...a.states,s,ac]),transitions:t,__highlightStates:[],__highlightEdges:[]};}
  function optionalNFA(a){const s=newStateId('q'),ac=newStateId('q'),t=cloneTransitions(a.transitions);t[s]=[{id:newEdgeId('e'),symbol:'ε',to:a.start},{id:newEdgeId('e'),symbol:'ε',to:ac}];t[a.accept]=t[a.accept]||[];t[a.accept].push({id:newEdgeId('e'),symbol:'ε',to:ac});t[ac]=t[ac]||[];return{type:'NFA',start:s,accept:ac,states:new Set([...a.states,s,ac]),transitions:t,__highlightStates:[],__highlightEdges:[]};}

  function buildThompson(pf){
    const st=[];
    for(const ch of pf){
      if(isOperand(ch))st.push(createSymbolNFA(ch));
      else if(ch==='.'){{const b=st.pop(),a=st.pop();if(!a||!b)throw new Error('Invalid regex');st.push(concatNFA(a,b));}}
      else if(ch==='|'){{const b=st.pop(),a=st.pop();if(!a||!b)throw new Error('Invalid regex');st.push(unionNFA(a,b));}}
      else if(ch==='*'){{const a=st.pop();if(!a)throw new Error('Invalid regex');st.push(starNFA(a));}}
      else if(ch==='+'){{const a=st.pop();if(!a)throw new Error('Invalid regex');st.push(plusNFA(a));}}
      else if(ch==='?'){{const a=st.pop();if(!a)throw new Error('Invalid regex');st.push(optionalNFA(a));}}
    }
    if(st.length!==1)throw new Error('Invalid regex');return st[0];
  }

  /* ========== Glushkov Construction (for clean NFA without epsilon) ========== */
  function postfixToAST(pf) {
    const st = []; let pos = 0;
    for (const ch of pf) {
      if (isOperand(ch)) st.push({ type:'sym', sym:ch, pos:pos++ });
      else if (ch==='.') { const r=st.pop(),l=st.pop(); st.push({type:'cat',l,r}); }
      else if (ch==='|') { const r=st.pop(),l=st.pop(); st.push({type:'alt',l,r}); }
      else if (ch==='*') st.push({type:'star',c:st.pop()});
      else if (ch==='+') st.push({type:'plus',c:st.pop()});
      else if (ch==='?') st.push({type:'opt',c:st.pop()});
    }
    return { ast: st[0], n: pos };
  }

  function gCollect(nd, p) {
    if (nd.type==='sym') { p[nd.pos]=nd.sym; }
    else if (nd.type==='cat'||nd.type==='alt') { gCollect(nd.l,p); gCollect(nd.r,p); }
    else gCollect(nd.c,p);
  }
  function gNull(nd) {
    if (nd.type==='sym') return nd.sym==='ε';
    if (nd.type==='cat') return gNull(nd.l)&&gNull(nd.r);
    if (nd.type==='alt') return gNull(nd.l)||gNull(nd.r);
    if (nd.type==='star'||nd.type==='opt') return true;
    if (nd.type==='plus') return gNull(nd.c);
  }
  function gFirst(nd) {
    if (nd.type==='sym') return nd.sym==='ε'?new Set():new Set([nd.pos]);
    if (nd.type==='cat') { const f=new Set(gFirst(nd.l)); if(gNull(nd.l)) for(const p of gFirst(nd.r))f.add(p); return f; }
    if (nd.type==='alt') { const f=new Set(gFirst(nd.l)); for(const p of gFirst(nd.r))f.add(p); return f; }
    return gFirst(nd.c);
  }
  function gLast(nd) {
    if (nd.type==='sym') return nd.sym==='ε'?new Set():new Set([nd.pos]);
    if (nd.type==='cat') { const l=new Set(gLast(nd.r)); if(gNull(nd.r)) for(const p of gLast(nd.l))l.add(p); return l; }
    if (nd.type==='alt') { const l=new Set(gLast(nd.l)); for(const p of gLast(nd.r))l.add(p); return l; }
    return gLast(nd.c);
  }
  function gFollow(nd, fw) {
    if (nd.type==='cat') {
      for (const p of gLast(nd.l)) for (const q of gFirst(nd.r)) fw[p].add(q);
      gFollow(nd.l,fw); gFollow(nd.r,fw);
    } else if (nd.type==='star'||nd.type==='plus') {
      for (const p of gLast(nd.c)) for (const q of gFirst(nd.c)) fw[p].add(q);
      gFollow(nd.c,fw);
    } else if (nd.type==='alt') { gFollow(nd.l,fw); gFollow(nd.r,fw); }
    else if (nd.type==='opt') gFollow(nd.c,fw);
  }

  function buildGlushkovNFA(rawRegex) {
    const concat = insertConcatOperators(rawRegex);
    const postfix = regexToPostfix(concat);
    const { ast, n } = postfixToAST(postfix);
    const posSyms = {}; gCollect(ast, posSyms);
    const fw = {}; for(let i=0;i<n;i++) fw[i]=new Set();
    gFollow(ast, fw);

    const states = new Set(['q0']);
    const tr = { 'q0': [] };
    for (let i=0;i<n;i++) { const nm=`q${i+1}`; states.add(nm); tr[nm]=[]; }

    // Start transitions
    for (const p of gFirst(ast))
      tr['q0'].push({ id:newEdgeId('e'), symbol:posSyms[p], to:`q${p+1}` });
    // Follow transitions
    for (let i=0;i<n;i++)
      for (const q of fw[i])
        tr[`q${i+1}`].push({ id:newEdgeId('e'), symbol:posSyms[q], to:`q${q+1}` });

    const acc = [...gLast(ast)].map(p=>`q${p+1}`);
    if (gNull(ast)) acc.push('q0');

    return { type:'NFA',start:'q0',accept:acc,states,transitions:tr,
      __highlightStates:[],__highlightEdges:[],__sourceSets:{},
      _concat:concat, _postfix:postfix };
  }

  /* ========== Epsilon Closure & NFA Ops ========== */
  function epsilonClosure(nfa,states){const cl=new Set(states),wl=[...states];while(wl.length){const s=wl.pop();for(const e of(nfa.transitions[s]||[]))if(e.symbol==='ε'&&!cl.has(e.to)){cl.add(e.to);wl.push(e.to);}}return cl;}
  function move(nfa,states,sym){const r=new Set();for(const s of states)for(const e of(nfa.transitions[s]||[]))if(e.symbol===sym)r.add(e.to);return r;}
  function nfaAlphabet(nfa){const s=new Set();for(const st in nfa.transitions)for(const e of nfa.transitions[st])if(e.symbol!=='ε')s.add(e.symbol);return[...s].sort();}
  function setKey(set){return[...set].sort().join(',')||'∅';}

  function convertNfaToDfa(nfa) {
    const alpha=nfaAlphabet(nfa),accSet=new Set(Array.isArray(nfa.accept)?nfa.accept:[nfa.accept]);
    const startCl=epsilonClosure(nfa,new Set([nfa.start])),queue=[startCl],seen=new Map(),src={},tr={},states=new Set(),accepts=[];let idx=0;
    function ensure(set){const k=setKey(set);if(!seen.has(k)){const id=`D${idx++}`;seen.set(k,id);states.add(id);src[id]=k;tr[id]=[];if([...set].some(s=>accSet.has(s)))accepts.push(id);}return seen.get(k);}
    ensure(startCl);for(let i=0;i<queue.length;i++){const cur=queue[i],cid=ensure(cur);
      for(const sym of alpha){const mv=move(nfa,cur,sym),cl=epsilonClosure(nfa,mv);if(!cl.size)continue;if(!seen.has(setKey(cl)))queue.push(cl);tr[cid].push({id:newEdgeId('de'),symbol:sym,to:ensure(cl)});}}
    return{type:'DFA',start:seen.get(setKey(startCl)),accept:accepts,states,transitions:tr,__sourceSets:src,__highlightStates:[],__highlightEdges:[]};
  }

  function simulateNFA(nfa,input){let cur=epsilonClosure(nfa,new Set([nfa.start]));for(const ch of input){cur=epsilonClosure(nfa,move(nfa,cur,ch));if(!cur.size)return false;}const ac=new Set(Array.isArray(nfa.accept)?nfa.accept:[nfa.accept]);return[...cur].some(s=>ac.has(s));}
  function simulateDFA(dfa,input){let cur=dfa.start;for(const ch of input){const n=(dfa.transitions[cur]||[]).find(e=>e.symbol===ch);if(!n)return false;cur=n.to;}return dfa.accept.includes(cur);}

  /* ========== Transition Table Rendering ========== */
  function renderNfaTransitionTable(machine) {
    const content = document.getElementById('nfaTransitionTableContent');
    content.innerHTML = '';
    const alpha = [];
    for (const s in machine.transitions)
      for (const e of machine.transitions[s])
        if (e.symbol !== 'ε' && !alpha.includes(e.symbol)) alpha.push(e.symbol);
    alpha.sort();
    // Check if epsilon transitions exist
    let hasEps = false;
    for (const s in machine.transitions)
      for (const e of machine.transitions[s])
        if (e.symbol === 'ε') { hasEps = true; break; }
    const cols = [...alpha]; if (hasEps) cols.push('ε');

    const accSet = new Set(Array.isArray(machine.accept) ? machine.accept : [machine.accept]);
    const stateList = [...machine.states].sort();
    const table = document.createElement('table');
    table.className = 'pda-table';
    const thead = document.createElement('thead');
    thead.innerHTML = `<tr><th>State</th>${cols.map(c => `<th>${c}</th>`).join('')}</tr>`;
    table.appendChild(thead);
    const tbody = document.createElement('tbody');
    for (const state of stateList) {
      const tr = document.createElement('tr');
      const pfx = (state===machine.start?'-> ':'') + (accSet.has(state)?'* ':'');
      let cells = `<td>${pfx}${state}</td>`;
      for (const sym of cols) {
        const tgts = (machine.transitions[state]||[]).filter(e=>e.symbol===sym).map(e=>e.to);
        const u = [...new Set(tgts)].sort();
        cells += `<td>${u.length ? '{'+u.join(', ')+'}' : '-'}</td>`;
      }
      tr.innerHTML = cells;
      tbody.appendChild(tr);
    }
    table.appendChild(tbody);
    content.appendChild(table);
    nfaTableSection.style.display = '';
  }

  /* ========== PDA Section ========== */
  function dSym(s){return s==='Z'?'z0':s;}
  function dPush(p){return p==='ε'?'ε':p.split('').map(dSym).join('');}
  function fmtPda(t){return`${dSym(t.input)}, ${dSym(t.pop)} / ${dPush(t.push)}`;}
  function dStack(stack){return stack.length===0?'(empty)':[...stack].reverse().map(dSym).join('');}

  function parseLangNotation(text) {
    const cleaned=text.replace(/\s+/g,''),segments=[],re=/([a-z])(?:\^(\d*)([a-z]))?/g;let m;
    while((m=re.exec(cleaned))!==null){const sym=m[1];if(m[3])segments.push({sym,coeff:m[2]?parseInt(m[2]):1,variable:m[3]});
      else if(m[2])segments.push({sym,coeff:parseInt(m[2]),variable:null});else segments.push({sym,coeff:1,variable:null});}
    if(!segments.length)throw new Error('Could not parse. Use format like a^n b^n');return segments;
  }
  function parseConstraints(text){const c={};if(!text||!text.trim())return c;for(const p of text.split(',')){const m=p.trim().match(/([a-z])\s*>=\s*(\d+)/);if(m)c[m[1]]=parseInt(m[2]);}return c;}

  let ptId=0;
  function pt(from,input,pop,push,to){return{id:`pt${ptId++}`,input,pop,push,to};}
  function makePDA(names,start,accept,trs){const states=new Set(names),tr={};for(const s of names)tr[s]=[];for(const t of trs){tr[t.from]=tr[t.from]||[];tr[t.from].push(t);}return{type:'PDA',states,start,accept:Array.isArray(accept)?accept:[accept],transitions:tr,initialStack:['Z']};}

  function buildSameVarPDA(s1,s2,minVal){
    ptId=0;const pushPer=s2.coeff,popPer=s1.coeff,sym1=s1.sym,sym2=s2.sym;
    const stk=sym1; // use lowercase terminal as stack counting symbol
    const allSt=['q0','q1','q2','qf'],trs=[];
    trs.push({from:'q0',...pt('q0',sym1,'Z',stk.repeat(pushPer)+'Z','q1')});
    trs.push({from:'q1',...pt('q1',sym1,stk,stk.repeat(pushPer+1),'q1')});
    if(popPer===1){trs.push({from:'q1',...pt('q1',sym2,stk,'ε','q2')});trs.push({from:'q2',...pt('q2',sym2,stk,'ε','q2')});}
    else{const mids=[];for(let i=0;i<popPer-1;i++){const nm=`qm${i}`;allSt.push(nm);mids.push(nm);}
      trs.push({from:'q1',...pt('q1',sym2,stk,'ε',mids[0])});
      for(let i=0;i<mids.length-1;i++)trs.push({from:mids[i],...pt(mids[i],'ε',stk,'ε',mids[i+1])});
      trs.push({from:mids[mids.length-1],...pt(mids[mids.length-1],'ε',stk,'ε','q2')});
      trs.push({from:'q2',...pt('q2',sym2,stk,'ε',mids[0])});}
    trs.push({from:'q2',...pt('q2','ε','Z','Z','qf')});
    if(minVal===0)trs.push({from:'q0',...pt('q0','ε','Z','Z','qf')});
    return makePDA(allSt,'q0','qf',trs);
  }
  function buildIndependentPDA(s1,s2,constraints){
    ptId=0;const sym1=s1.sym,sym2=s2.sym,min1=constraints[s1.variable]||0,min2=constraints[s2.variable]||0;
    const allSt=['q0','qf'],trs=[];
    if(min1>=1){allSt.push('q1','q2');trs.push({from:'q0',...pt('q0',sym1,'Z','Z','q1')});trs.push({from:'q1',...pt('q1',sym1,'Z','Z','q1')});
      if(min2>=1){trs.push({from:'q1',...pt('q1',sym2,'Z','Z','q2')});trs.push({from:'q2',...pt('q2',sym2,'Z','Z','q2')});trs.push({from:'q2',...pt('q2','ε','Z','Z','qf')});}
      else{trs.push({from:'q1',...pt('q1',sym2,'Z','Z','q1')});trs.push({from:'q1',...pt('q1','ε','Z','Z','qf')});}}
    else{allSt.push('q1');trs.push({from:'q0',...pt('q0',sym1,'Z','Z','q0')});
      if(min2>=1){trs.push({from:'q0',...pt('q0',sym2,'Z','Z','q1')});trs.push({from:'q1',...pt('q1',sym2,'Z','Z','q1')});trs.push({from:'q1',...pt('q1','ε','Z','Z','qf')});}
      else{trs.push({from:'q0',...pt('q0',sym2,'Z','Z','q0')});trs.push({from:'q0',...pt('q0','ε','Z','Z','qf')});}}
    return makePDA(allSt,'q0','qf',trs);
  }
  function buildWcwRPDA(){ptId=0;const t=[];for(const x of['a','b']){t.push({from:'q0',...pt('q0',x,'Z',x+'Z','q0')});for(const top of['a','b'])t.push({from:'q0',...pt('q0',x,top,x+top,'q0')});}
    for(const top of['a','b','Z'])t.push({from:'q0',...pt('q0','c',top,top,'q1')});
    t.push({from:'q1',...pt('q1','a','a','ε','q1')});t.push({from:'q1',...pt('q1','b','b','ε','q1')});t.push({from:'q1',...pt('q1','ε','Z','Z','qf')});return makePDA(['q0','q1','qf'],'q0','qf',t);}
  function buildWwRPDA(){ptId=0;const t=[];for(const x of['a','b']){t.push({from:'q0',...pt('q0',x,'Z',x+'Z','q0')});for(const top of['a','b'])t.push({from:'q0',...pt('q0',x,top,x+top,'q0')});}
    for(const top of['a','b','Z'])t.push({from:'q0',...pt('q0','ε',top,top,'q1')});
    t.push({from:'q1',...pt('q1','a','a','ε','q1')});t.push({from:'q1',...pt('q1','b','b','ε','q1')});t.push({from:'q1',...pt('q1','ε','Z','Z','qf')});t.push({from:'q0',...pt('q0','ε','Z','Z','qf')});return makePDA(['q0','q1','qf'],'q0','qf',t);}
  function buildEqualCountPDA(){ptId=0;const t=[];
    t.push({from:'q0',...pt('q0','a','Z','aZ','q0')});t.push({from:'q0',...pt('q0','a','a','aa','q0')});t.push({from:'q0',...pt('q0','a','b','ε','q0')});
    t.push({from:'q0',...pt('q0','b','Z','bZ','q0')});t.push({from:'q0',...pt('q0','b','b','bb','q0')});t.push({from:'q0',...pt('q0','b','a','ε','q0')});
    t.push({from:'q0',...pt('q0','ε','Z','Z','qf')});return makePDA(['q0','qf'],'q0','qf',t);}
  function buildExponentPDA(segs,constraints){
    if(segs.length<1||segs.length>2)throw new Error('Use 1 or 2 segments, e.g. a^n b^n');
    if(segs.length===1){ptId=0;const s=segs[0],t=[];t.push({from:'q0',...pt('q0',s.sym,'Z','Z','q0')});t.push({from:'q0',...pt('q0','ε','Z','Z','qf')});return makePDA(['q0','qf'],'q0','qf',t);}
    const[s1,s2]=segs;
    if(s1.variable&&s2.variable&&s1.variable===s2.variable)return buildSameVarPDA(s1,s2,constraints[s1.variable]||0);
    return buildIndependentPDA(s1,s2,constraints);
  }

  function simulatePDA(pda,inputStr){
    const MAX=100000,visited=new Set(),initStack=[...pda.initialStack];
    const queue=[{state:pda.start,pos:0,stack:initStack,trace:[{state:pda.start,read:'-',stack:[...initStack],action:'Start'}]}];let count=0;
    while(queue.length&&count<MAX){const cfg=queue.shift();count++;
      if(pda.accept.includes(cfg.state)&&cfg.pos>=inputStr.length)return{accepted:true,trace:cfg.trace};
      const sk=cfg.stack.length<=50?cfg.stack.join(''):cfg.stack.slice(-50).join('');const key=`${cfg.state}|${cfg.pos}|${sk}`;if(visited.has(key))continue;visited.add(key);
      for(const t of(pda.transitions[cfg.state]||[])){let np=cfg.pos;if(t.input==='ε'){}else if(cfg.pos<inputStr.length&&inputStr[cfg.pos]===t.input)np=cfg.pos+1;else continue;
        const ns=[...cfg.stack];if(t.pop==='ε'){}else if(ns.length&&ns[ns.length-1]===t.pop)ns.pop();else continue;
        if(t.push!=='ε')for(let i=t.push.length-1;i>=0;i--)ns.push(t.push[i]);if(ns.length>300)continue;
        queue.push({state:t.to,pos:np,stack:ns,trace:[...cfg.trace,{state:t.to,read:t.input==='ε'?'ε':t.input,stack:[...ns],action:fmtPda(t)}]});}}
    return{accepted:false,trace:[]};
  }

  /* ========== SVG Drawing ========== */
  function clearSvg(){while(svg.firstChild)svg.removeChild(svg.firstChild);}
  function createSvg(tag,attrs){const el=document.createElementNS(SVG_NS,tag);if(attrs)for(const[k,v]of Object.entries(attrs))el.setAttribute(k,v);return el;}
  function addDefs(){
    const defs=createSvg('defs');
    const arrow=createSvg('marker',{id:'arrowHead',markerWidth:'16',markerHeight:'12',refX:'13',refY:'6',orient:'auto',markerUnits:'userSpaceOnUse'});
    arrow.appendChild(createSvg('path',{d:'M2,2 L13,6 L2,10',fill:'none',stroke:EDGE_COLOR,'stroke-width':'2','stroke-linecap':'round','stroke-linejoin':'round'}));defs.appendChild(arrow);
    const arrowS=createSvg('marker',{id:'arrowStart',markerWidth:'16',markerHeight:'12',refX:'13',refY:'6',orient:'auto',markerUnits:'userSpaceOnUse'});
    arrowS.appendChild(createSvg('path',{d:'M2,2 L13,6 L2,10',fill:'none',stroke:'#475569','stroke-width':'2','stroke-linecap':'round','stroke-linejoin':'round'}));defs.appendChild(arrowS);
    const f=createSvg('filter',{id:'stateShadow',x:'-25%',y:'-25%',width:'150%',height:'150%'});
    f.appendChild(createSvg('feDropShadow',{dx:'0',dy:'1',stdDeviation:'2','flood-color':'rgba(0,0,0,0.08)'}));defs.appendChild(f);
    svg.appendChild(defs);
  }

  function computePositions(machine){
    const dist={},q=[machine.start];dist[machine.start]=0;
    while(q.length){const s=q.shift();for(const e of(machine.transitions[s]||[]))if(dist[e.to]==null){dist[e.to]=dist[s]+1;q.push(e.to);}}
    let fb=0;for(const s of machine.states)if(dist[s]==null)dist[s]=++fb;
    const groups=new Map();for(const s of machine.states){const l=dist[s]||0;if(!groups.has(l))groups.set(l,[]);groups.get(l).push(s);}
    const sorted=[...groups.keys()].sort((a,b)=>a-b),pos={},pL=100,pR=120,pT=90,pB=80,uW=VIEW_W-pL-pR,uH=VIEW_H-pT-pB;
    const gL=sorted.length<=1?0:uW/(sorted.length-1);
    sorted.forEach((lvl,i)=>{const sts=groups.get(lvl).sort(),x=pL+i*gL,gS=sts.length<=1?0:uH/(sts.length-1);
      sts.forEach((s,j)=>{pos[s]={x,y:sts.length<=1?VIEW_H/2:pT+j*gS};});});
    return pos;
  }

  function drawMachine(machine){
    clearSvg();svg.setAttribute('viewBox',`0 0 ${VIEW_W} ${VIEW_H}`);addDefs();
    const positions=computePositions(machine);
    const acceptSet=new Set(Array.isArray(machine.accept)?machine.accept:[machine.accept]);
    // Merge edges
    const eg={};for(const from in machine.transitions)for(const edge of machine.transitions[from]){
      const k=`${from}->${edge.to}`;if(!eg[k])eg[k]={from,to:edge.to,labels:[]};eg[k].labels.push(edge.symbol);}
    const dp=new Map();
    for(const k in eg){const g=eg[k],rev=!!eg[`${g.to}->${g.from}`]&&g.from!==g.to;
      const pk=`${g.from}->${g.to}`,cnt=(dp.get(pk)||0)+1;dp.set(pk,cnt);
      if(g.from===g.to){
        // Self-loop: draw with label box
        drawSelfLoopBox(g.from,g.labels,positions,machine.type==='PDA');
      } else {
        const sep = machine.type==='PDA' ? ' | ' : ', ';
        const lbl=g.labels.length<=3?g.labels.join(sep):g.labels.slice(0,3).join(sep)+` (+${g.labels.length-3})`;
        const sm=machine.type==='PDA';drawEdge(g.from,g.to,lbl,positions,cnt,rev,sm);
      }}
    for(const s of machine.states)drawState(s,positions[s],{isStart:s===machine.start,isAccept:acceptSet.has(s),
      subtitle:machine.type==='DFA'&&machine.__sourceSets?.[s]?machine.__sourceSets[s]:null});
  }

  function drawSelfLoopBox(state,labels,positions,isPDA){
    const pos=positions[state];if(!pos)return;
    const rng=seedRandom(hashStr(state+'_sl')),w=2;
    // Draw the arc
    svg.appendChild(createSvg('path',{d:`M ${pos.x-14} ${pos.y-RADIUS+2} C ${pos.x-40+(rng()-.5)*w} ${pos.y-72+(rng()-.5)*w}, ${pos.x+40+(rng()-.5)*w} ${pos.y-72+(rng()-.5)*w}, ${pos.x+14} ${pos.y-RADIUS}`,
      fill:'none',stroke:EDGE_COLOR,'stroke-width':'1.8','stroke-linecap':'round','marker-end':'url(#arrowHead)'}));
    // If few labels and short, render inline
    const joined=labels.join(isPDA ? ' | ' : ', ');
    if(labels.length<=2&&joined.length<=40){
      svg.appendChild(Object.assign(createSvg('text',{x:pos.x,y:pos.y-78,class:isPDA?'edge-label-small':'edge-label'}),{textContent:joined}));
      return;
    }
    // Label box for many/long labels
    const lineH=15,padV=6,padH=10;
    const totalH=labels.length*lineH+padV*2;
    const maxLen=Math.max(...labels.map(l=>l.length));
    const boxW=Math.max(maxLen*6.5+padH*2,100);
    const boxX=pos.x-boxW/2,boxY=pos.y-78-totalH-4;
    // Background rect
    svg.appendChild(createSvg('rect',{x:boxX,y:boxY,width:boxW,height:totalH,rx:'5',
      fill:'#ffffff',stroke:'#cbd5e1','stroke-width':'1'}));
    // Each label line
    labels.forEach((lbl,i)=>{
      svg.appendChild(Object.assign(createSvg('text',{x:pos.x,y:boxY+padV+11+i*lineH,
        class:'edge-label-small'}),{textContent:lbl}));
    });
    // Connector line from box to arc
    svg.appendChild(createSvg('line',{x1:pos.x,y1:boxY+totalH,x2:pos.x,y2:pos.y-75,
      stroke:'#cbd5e1','stroke-width':'1','stroke-dasharray':'3,3'}));
  }

  function drawEdge(from,to,label,positions,occ,rev,small){
    const p1=positions[from],p2=positions[to];if(!p1||!p2)return;
    const seed=hashStr(from+to+String(occ)),rng=seedRandom(seed),sw='1.8',cls=small?'edge-label-small':'edge-label';
    const dx=p2.x-p1.x,dy=p2.y-p1.y,len=Math.hypot(dx,dy)||1,ux=dx/len,uy=dy/len;
    const sx=p1.x+ux*RADIUS,sy=p1.y+uy*RADIUS,ex=p2.x-ux*(RADIUS+3),ey=p2.y-uy*(RADIUS+3);
    let off=0;if(rev)off=28;if(occ>1)off+=occ*12;
    const px=-uy,py=ux,wb=Math.min(len*.012,2.5);
    const cx=(sx+ex)/2+px*off+(rng()-.5)*wb*2,cy=(sy+ey)/2+py*off+(rng()-.5)*wb*2;
    svg.appendChild(createSvg('path',{d:`M ${sx} ${sy} Q ${cx} ${cy} ${ex} ${ey}`,fill:'none',stroke:EDGE_COLOR,'stroke-width':sw,'stroke-linecap':'round','marker-end':'url(#arrowHead)'}));
    const lx=.25*sx+.5*cx+.25*ex,ly=.25*sy+.5*cy+.25*ey-8;
    svg.appendChild(Object.assign(createSvg('text',{x:lx,y:ly,class:cls}),{textContent:label}));
  }

  function drawState(id,pos,{isStart,isAccept,subtitle}){
    if(!pos)return;const g=createSvg('g'),fill=isStart?START_COLOR:isAccept?ACCEPT_COLOR:NORMAL_COLOR;
    if(isStart){const sd=seedRandom(hashStr(id+'_st')),x1=pos.x-55,x2=pos.x-RADIUS-4;
      g.appendChild(createSvg('path',{d:`M ${x1} ${pos.y} Q ${(x1+x2)/2} ${pos.y+(sd()-.5)} ${x2} ${pos.y}`,fill:'none',stroke:'#475569','stroke-width':'1.8','stroke-linecap':'round','marker-end':'url(#arrowStart)'}));}
    g.appendChild(createSvg('circle',{cx:pos.x,cy:pos.y,r:RADIUS,fill,stroke:'#1e293b','stroke-width':'1.5',filter:'url(#stateShadow)'}));
    if(isAccept)g.appendChild(createSvg('circle',{cx:pos.x,cy:pos.y,r:RADIUS-6,fill:'none',stroke:'white','stroke-width':'2'}));
    g.appendChild(Object.assign(createSvg('text',{x:pos.x,y:pos.y,class:'state-label'}),{textContent:id}));
    if(subtitle){const sub=createSvg('text',{x:pos.x,y:pos.y+44,'text-anchor':'middle','font-size':'11',fill:'#64748b','font-weight':'600'});sub.textContent=`{${subtitle==='∅'?'':subtitle}}`;g.appendChild(sub);}
    svg.appendChild(g);
  }

  function preparePDAForDrawing(pda){
    const out={};
    for(const from in pda.transitions){
      out[from]=[];
      for(const t of pda.transitions[from])
        out[from].push({id:t.id,symbol:fmtPda(t),to:t.to});
    }
    return{type:'PDA',start:pda.start,accept:pda.accept,states:pda.states,transitions:out,__highlightStates:[],__highlightEdges:[],__sourceSets:{}};
  }
  function renderPdaTable(pda){
    const content=document.getElementById('transitionTableContent');content.innerHTML='';
    const table=document.createElement('table');table.className='pda-table';
    table.innerHTML='<thead><tr><th>State</th><th>Input</th><th>Pop</th><th>Next State</th><th>Push</th></tr></thead>';
    const tbody=document.createElement('tbody'),stateOrder=[...pda.states].sort();
    for(const st of stateOrder)for(const t of(pda.transitions[st]||[])){const tr=document.createElement('tr');tr.innerHTML=`<td>${st}</td><td>${dSym(t.input)}</td><td>${dSym(t.pop)}</td><td>${t.to}</td><td>${dPush(t.push)}</td>`;tbody.appendChild(tr);}
    table.appendChild(tbody);content.appendChild(table);pdaTableSection.style.display='';
  }
  function renderSimTrace(result){
    const content=document.getElementById('simTraceContent');content.innerHTML='';
    if(!result.trace.length){content.textContent='No accepting path found.';pdaTraceSection.style.display='';return;}
    const table=document.createElement('table');table.className='pda-table';
    table.innerHTML='<thead><tr><th>Step</th><th>Read</th><th>State</th><th>Stack (top left)</th><th>Transition</th></tr></thead>';
    const tbody=document.createElement('tbody'),max=Math.min(result.trace.length,50);
    for(let i=0;i<max;i++){const s=result.trace[i],tr=document.createElement('tr');if(i===max-1&&result.accepted)tr.className='trace-accept';
      tr.innerHTML=`<td>${i}</td><td>${s.read}</td><td>${s.state}</td><td class="stack-display">${dStack(s.stack)}</td><td>${s.action}</td>`;tbody.appendChild(tr);}
    table.appendChild(tbody);content.appendChild(table);pdaTraceSection.style.display='';
  }

  /* ========== Build Handlers ========== */
  function buildHandler(){if(currentMode==='epsilon-nfa')buildEpsilonNFA();else if(currentMode==='nfa')buildNFAHandler();}

  function buildEpsilonNFA(){
    builtNfa=null;builtDfa=null;showResult(resultView,'-','result-info');nfaTableSection.style.display='none';
    try{resetIds();const raw=regexInput.value.trim();if(!raw)throw new Error('Regex cannot be empty');
      const concat=insertConcatOperators(raw),pf=regexToPostfix(concat);concatView.textContent=concat;postfixView.textContent=pf;
      const nfa=buildThompson(pf);nfa.__highlightStates=[];nfa.__highlightEdges=[];builtNfa=cloneMachine(nfa);
      stepDescription.textContent='Epsilon-NFA built using Thompson\'s construction.';
      drawMachine(builtNfa);renderNfaTransitionTable(builtNfa);
      resetBtn.disabled=false;convertBtn.disabled=false;simulateNfaBtn.disabled=false;simulateDfaBtn.disabled=true;
    }catch(e){handleBuildErr(e);}
  }

  function buildNFAHandler(){
    builtNfa=null;builtDfa=null;showResult(resultView,'-','result-info');nfaTableSection.style.display='none';
    try{resetIds();const raw=regexInput.value.trim();if(!raw)throw new Error('Regex cannot be empty');
      const nfa=buildGlushkovNFA(raw);builtNfa=cloneMachine(nfa);
      concatView.textContent=nfa._concat||'-';postfixView.textContent=nfa._postfix||'-';
      stepDescription.textContent='NFA built using Glushkov (position automaton) construction -- minimal states, no epsilon transitions.';
      drawMachine(builtNfa);renderNfaTransitionTable(builtNfa);
      resetBtn.disabled=false;convertBtn.disabled=false;simulateNfaBtn.disabled=false;simulateDfaBtn.disabled=true;
    }catch(e){handleBuildErr(e);}
  }

  function handleBuildErr(err){stepDescription.textContent=`Error: ${err.message}`;clearSvg();drawPlaceholder();
    resetBtn.disabled=true;convertBtn.disabled=true;simulateNfaBtn.disabled=true;simulateDfaBtn.disabled=true;
    concatView.textContent='-';postfixView.textContent='-';showResult(resultView,'Build failed','result-rejected');nfaTableSection.style.display='none';}

  function convertToDFA(){if(!builtNfa)return;builtDfa=convertNfaToDfa(builtNfa);drawMachine(builtDfa);renderNfaTransitionTable(builtDfa);
    stepDescription.textContent='DFA created using subset construction.';simulateDfaBtn.disabled=false;showResult(resultView,'DFA created','result-info');}

  function buildPDAHandler(){
    builtPda=null;showResult(pdaResultView,'-','result-info');pdaTraceSection.style.display='none';
    try{const pdaType=document.querySelector('input[name="pdaType"]:checked').value;let pda,langDesc;
      if(pdaType==='exponent'){const lt=langInput.value.trim();if(!lt)throw new Error('Enter a language');const segs=parseLangNotation(lt),cons=parseConstraints(constraintInput.value);pda=buildExponentPDA(segs,cons);
        const cStr=Object.entries(cons).map(([v,m])=>`${v} >= ${m}`).join(', ');langDesc=`{ ${lt}${cStr?' | '+cStr:''} }`;}
      else{const p=wordPattern.value;if(p==='wcwR'){pda=buildWcwRPDA();langDesc='{ wcw^R | w in {a,b}* }';}
        else if(p==='wwR'){pda=buildWwRPDA();langDesc='{ ww^R | w in {a,b}* }';}
        else if(p==='equalAB'){pda=buildEqualCountPDA();langDesc='{ w in {a,b}* | #a = #b }';}
        else throw new Error('Unknown pattern');}
      builtPda=pda;langDescView.textContent=langDesc;initStackView.textContent='z0';
      pdaDescription.textContent='PDA constructed. See transition table below.';
      drawMachine(preparePDAForDrawing(pda));renderPdaTable(pda);
      resetPdaBtn.disabled=false;simulatePdaBtn.disabled=false;
    }catch(err){pdaDescription.textContent=`Error: ${err.message}`;clearSvg();drawPlaceholder();pdaTableSection.style.display='none';
      resetPdaBtn.disabled=true;simulatePdaBtn.disabled=true;langDescView.textContent='-';initStackView.textContent='-';showResult(pdaResultView,'Build failed','result-rejected');}
  }

  function runSim(){if(!builtNfa)return;const ok=simulateNFA(builtNfa,stringInput.value);const l=currentMode==='epsilon-nfa'?'Epsilon-NFA':'NFA';
    showResult(resultView,ok?`Accepted by ${l}`:`Rejected by ${l}`,ok?'result-accepted':'result-rejected');}
  function runDfaSim(){if(!builtDfa)return;const ok=simulateDFA(builtDfa,stringInput.value);showResult(resultView,ok?'Accepted by DFA':'Rejected by DFA',ok?'result-accepted':'result-rejected');}
  function runPdaSim(){if(!builtPda)return;const r=simulatePDA(builtPda,pdaStringInput.value);
    showResult(pdaResultView,r.accepted?'Accepted by PDA':'Rejected by PDA',r.accepted?'result-accepted':'result-rejected');renderSimTrace(r);}

  function resetView(){builtNfa=null;builtDfa=null;drawPlaceholder();stepDescription.textContent='Enter a regex and click Build.';
    concatView.textContent='-';postfixView.textContent='-';showResult(resultView,'-','result-info');
    resetBtn.disabled=true;convertBtn.disabled=true;simulateNfaBtn.disabled=true;simulateDfaBtn.disabled=true;nfaTableSection.style.display='none';}
  function resetPdaView(){builtPda=null;drawPlaceholder();pdaDescription.textContent='Choose a language type and define a language to build a PDA.';
    langDescView.textContent='-';initStackView.textContent='-';showResult(pdaResultView,'-','result-info');
    pdaTableSection.style.display='none';pdaTraceSection.style.display='none';resetPdaBtn.disabled=true;simulatePdaBtn.disabled=true;}

  function switchMode(mode){currentMode=mode;document.querySelectorAll('.mode-tab').forEach(t=>t.classList.toggle('active',t.dataset.mode===mode));
    regexPanel.style.display=mode==='pda'?'none':'';pdaPanel.style.display=mode==='pda'?'':'none';
    regexGuide.style.display=mode==='pda'?'none':'';pdaGuide.style.display=mode==='pda'?'':'none';
    pdaTableSection.style.display='none';pdaTraceSection.style.display='none';nfaTableSection.style.display='none';
    if(mode==='epsilon-nfa')buildBtn.textContent='Build Epsilon-NFA';else if(mode==='nfa')buildBtn.textContent='Build NFA';
    builtNfa=null;builtDfa=null;builtPda=null;resetBtn.disabled=true;convertBtn.disabled=true;
    simulateNfaBtn.disabled=true;simulateDfaBtn.disabled=true;resetPdaBtn.disabled=true;simulatePdaBtn.disabled=true;
    showResult(resultView,'-','result-info');showResult(pdaResultView,'-','result-info');
    stepDescription.textContent='Enter a regex and click Build.';pdaDescription.textContent='Choose a language type and define a language to build a PDA.';
    concatView.textContent='-';postfixView.textContent='-';langDescView.textContent='-';initStackView.textContent='-';drawPlaceholder();}

  function drawPlaceholder(){clearSvg();svg.setAttribute('viewBox',`0 0 ${VIEW_W} ${VIEW_H}`);
    const t=createSvg('text',{x:VIEW_W/2,y:VIEW_H/2,'text-anchor':'middle','font-size':'22',fill:'#94a3b8','font-weight':'600','font-family':"'Inter',sans-serif"});
    t.textContent=currentMode==='pda'?'Define a language and click Build PDA':'Enter a regex and click Build to see the automaton';svg.appendChild(t);}

  buildBtn.addEventListener('click',buildHandler);resetBtn.addEventListener('click',resetView);convertBtn.addEventListener('click',convertToDFA);
  simulateNfaBtn.addEventListener('click',runSim);simulateDfaBtn.addEventListener('click',runDfaSim);
  buildPdaBtn.addEventListener('click',buildPDAHandler);resetPdaBtn.addEventListener('click',resetPdaView);simulatePdaBtn.addEventListener('click',runPdaSim);
  document.querySelectorAll('.mode-tab').forEach(tab=>tab.addEventListener('click',()=>switchMode(tab.dataset.mode)));
  document.querySelectorAll('input[name="pdaType"]').forEach(r=>r.addEventListener('change',()=>{exponentInputs.style.display=r.value==='exponent'?'':'none';wordInputs.style.display=r.value==='word'?'':'none';}));

  window.loadExample=function(regex){regexInput.value=regex;buildBtn.click();};
  window.loadPdaExample=function(name){
    const exp={'anbn':['a^n b^n','n >= 1'],'a2nbn':['a^2n b^n','n >= 1'],'anb2n':['a^n b^2n','n >= 1'],'anbm':['a^n b^m','n >= 1, m >= 1']};
    if(exp[name]){document.querySelector('input[name="pdaType"][value="exponent"]').checked=true;exponentInputs.style.display='';wordInputs.style.display='none';langInput.value=exp[name][0];constraintInput.value=exp[name][1];buildPdaBtn.click();}
    else{document.querySelector('input[name="pdaType"][value="word"]').checked=true;exponentInputs.style.display='none';wordInputs.style.display='';wordPattern.value={'wcwR':'wcwR','wwR':'wwR','equalAB':'equalAB'}[name]||'wcwR';buildPdaBtn.click();}};

  drawPlaceholder();
})();
