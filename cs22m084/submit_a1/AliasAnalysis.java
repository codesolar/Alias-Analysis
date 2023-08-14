package submit_a1;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;

import com.google.common.collect.Sets;

import dont_submit.AliasQuery;
import javafx.util.Pair;
import soot.ArrayType;
import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.PatchingChain;
import soot.RefLikeType;
import soot.RefType;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.UnitPatchingChain;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.GotoStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewExpr;
import soot.jimple.RetStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.Stmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JimpleLocal;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.util.Chain;

public class  AliasAnalysis extends BodyTransformer{

	int count = 1;
	Map<String,Set<String>> stackG = null;
	Map<Pair<String,String>,Set<String>> heapG = null;
	Map<Unit,String> visitedNewStmt = null;
	Map<String,Type> objType = null;
	Map<String,Set<String>> finalstackG = null;
	Map<Pair<String,String>,Set<String>> finalheapG = null;
	Set<String> formalParams = null;
	Set<Unit> setOfReturns = null;
	void Flow(Unit unit) {

		Stmt stmt = (Stmt)unit;
		
		//System.out.println("IN FLOW    " + stmt);
		if(stmt instanceof DefinitionStmt) {
			//System.out.println("INSIDE THE DEFINITION STMT BLOCK");
			Value lhs = ((DefinitionStmt) stmt).getLeftOp();
			Value rhs = ((DefinitionStmt) stmt).getRightOp();

			if(rhs instanceof NewExpr) {
				if(visitedNewStmt.containsKey(unit)) {
					String l = lhs.toString();
					Set<String> set;
					set = new HashSet<>();
					String obj = visitedNewStmt.get(unit);
					set.add(obj);
					stackG.put(l, set);
				}
				else {
					//System.out.println("sentence type is = x = new");
					String l = lhs.toString();
					Set<String> set;
					set = new HashSet<>();
					
					//object type store and visited update
					String obj = "R" + count;
					count++;
					objType.put(obj, rhs.getType());
					visitedNewStmt.put(unit, obj);
					
					
					set.add(obj);
					stackG.put(l,set);
				}
			}
			

			else if(rhs instanceof NewArrayExpr) {
				if(visitedNewStmt.containsKey(unit)) {
					String l = lhs.toString();
					Set<String> set;
					set = new HashSet<>();
					String obj = visitedNewStmt.get(unit);
					set.add(obj);
					stackG.put(l, set);
				}
				else {
					//System.out.println("sentence type is a = new []");
					String l = lhs.toString();
					Set<String> set;
					set = new HashSet<>();

			        String obj = "R" + count;
					count++;
					objType.put(obj, rhs.getType());
					visitedNewStmt.put(unit, obj);
					
					set.add(obj);
					stackG.put(l,set);
				}
			}
			
			else if(lhs instanceof InstanceFieldRef && !(rhs instanceof InstanceFieldRef)) {
				//System.out.println("sentence type is = x.f = y");
				InstanceFieldRef IFR = (InstanceFieldRef)lhs;
				String l = IFR.getBase().toString();
				String f = IFR.getField().getName();
				String r = rhs.toString();
				if(!stackG.containsKey(l) || !stackG.containsKey(r)) return;
				
				Set<String> setL = stackG.get(l);
				Set<String> setR = stackG.get(r);
				
				if(setL.size() == 1 && setL.iterator().next().equals("bottom")) {
					return;
				}
				else if(setL.size() == 1) {//strong update
					Pair<String,String> p = new Pair<String,String>(setL.iterator().next(),f);
					Set<String> set = new HashSet<>();
					set.addAll(setR);
					heapG.put(p, set);
				}
				else {//weak update
					for(String str:setL) {
						Pair<String,String> p = new Pair<String,String>(str,f);
						if(heapG.containsKey(p)) {
							Set<String> set = heapG.get(p);
							//here set can contain bottom too
							if(set.size() > 1 || !set.iterator().next().equals("bottom")) {
								if(setR.size() == 1 && setR.iterator().next().equals("bottom")) {
									set = new HashSet<>();
									set.add("bottom");
								}
								else {
									set = Sets.union(set , setR);
								}
						
								heapG.put(p, set);
							}
						}
						else {//here I am simply pushing setR, not checking anything else
							Set<String> set = new HashSet<>();
							//here set is the new set. not setR. so changed in the heap
							set.addAll(setR);
							heapG.put(p, set);
						}
					}
				}
			}
			
			else if(!(lhs instanceof InstanceFieldRef) && rhs instanceof InstanceFieldRef) {
				
				//System.out.println("sentence type is = x = y.f");
				if(!(lhs.getType() instanceof RefLikeType)) {
					return;
				}
				String l = lhs.toString();
				InstanceFieldRef IFR = (InstanceFieldRef)rhs;
				String r = IFR.getBase().toString();
				String f = IFR.getField().getName();
				if(!stackG.containsKey(r)) return;
				Set<String> setR = stackG.get(r);
				Set<String> setL = new HashSet<>();
				if(setR.size() == 1 && setR.iterator().next().equals("bottom")) {
					setL.add("bottom");
				}
				else {
					for(String str:setR) {
						if(setL.size() == 1 && setL.iterator().next().equals("bottom")) {
							break;
						}
						else {
							Pair<String,String> p = new Pair<String,String>(str,f);
							if(!heapG.containsKey(p)) {
								continue;
							}
							else {
								Set<String> set = heapG.get(p);
								if(set.size() == 1 && set.iterator().next().equals("bottom")) {
									setL = new HashSet<>();
									setL.add("bottom");
								}
								else {
									setL = Sets.union(setL, set);
								}
							}
						}
					}
				}
				
				
				if(setL.size() != 0) {
					stackG.put(l, setL);
				}
			}

			else if(rhs instanceof InstanceInvokeExpr) {
				//System.out.println("sentence type is = x = y.foo()");
				InstanceInvokeExpr expr = (InstanceInvokeExpr)rhs;
				String l = lhs.toString();
				//System.out.println(l);
				Value base = expr.getBase();
				String r = base.toString();
				String methodName = expr.getMethod().getName();
				//System.out.println(methodName);
				if(!stackG.containsKey(r)) return;
				Set<String> setR = stackG.get(r);

				SootClass currentClass = null;
				//for the base variable the fields are set to bottom
				
				if(setR.size() != 1 || !setR.iterator().next().equals("bottom")) {
					for(String str:setR) {
						Type type = objType.get(str);
						if(type instanceof RefType) {
							RefType reftype = (RefType)type;
							currentClass = reftype.getSootClass();
							Chain<SootField> chain = currentClass.getFields();
							Set<SootField> setOfChain = new HashSet<>();
							for(SootField sf:chain) {
								if(sf.getType() instanceof RefLikeType)
									setOfChain.add(sf);
							}
							//System.out.println("CURRENT CLASS = " + currentClass);
							//System.out.println("CHAIN SIZE" + setOfChain.size());
							while(currentClass.hasSuperclass()) {
								currentClass = currentClass.getSuperclass();
								//System.out.println("PARENT CLASS = " + currentClass);
								Chain<SootField> chain2 = currentClass.getFields();
								for(SootField sf:chain2) {
									if(sf.getType() instanceof RefLikeType)
										setOfChain.add(sf);
								}
							}
							//System.out.println("CHAIN SIZE" + setOfChain.size());
							//System.out.println(chain.size());
							
							for(SootField f:setOfChain) {
								Pair<String,String> p = new Pair<String,String>(str,f.getName());
								Set<String> FieldSet = new HashSet<>();
								FieldSet.add("bottom");
								heapG.put(p, FieldSet);
							}
						}
					}
				}
				

				

				
				
				

				List<Value> args = expr.getArgs();
				for(Value arg:args) {
					if(!stackG.containsKey(arg.toString())) continue;
					Set<String> setArgObj = stackG.get(arg.toString());
					if(setArgObj.size() != 1 || !setArgObj.iterator().next().equals("bottom")) {
						for(String str:setArgObj) {
							Type type = objType.get(str);
							if(type instanceof RefType) {
								RefType reftype = (RefType)type;
								currentClass = reftype.getSootClass();
								Chain<SootField> chain = currentClass.getFields();
								Set<SootField> setOfChain = new HashSet<>();
								for(SootField sf:chain) {
									setOfChain.add(sf);
								}
								//System.out.println("CURRENT CLASS = " + currentClass);
								//System.out.println("CHAIN SIZE" + setOfChain.size());
								while(currentClass.hasSuperclass()) {
									currentClass = currentClass.getSuperclass();
									//System.out.println("PARENT CLASS = " + currentClass);
									Chain<SootField> chain2 = currentClass.getFields();
									for(SootField sf:chain2) {
										setOfChain.add(sf);
									}
								}
								//System.out.println("CHAIN SIZE" + setOfChain.size());
								for(SootField f:setOfChain) {
									Pair<String,String> p = new Pair<String,String>(str,f.getName());
									Set<String> FieldSet = new HashSet<>();
									FieldSet.add("bottom");
									heapG.put(p, FieldSet);
								}
							}
						}
					}
				}

				
				
				//for the lhs , it is bottom
				if(!(lhs.getType() instanceof RefLikeType)) {
					return;
				}
				Set<String> setL = new HashSet<>();
				setL.add("bottom");
				stackG.put(l, setL);



				
			}
			else if(!(lhs instanceof InstanceFieldRef) && !(rhs instanceof InstanceFieldRef)) {
				//System.out.println("sentence type is = x = y");
				if(!(lhs.getType() instanceof RefLikeType)) {
					return;
				}
				String l = lhs.toString();
				String r = rhs.toString();
				//System.out.println(l + "    " + r);
				Set<String> setL = new HashSet<>();
				if(!stackG.containsKey(r)) return ;
				Set<String> setR = stackG.get(r);
				//System.out.println("HERe");
				setL.addAll(setR);
				stackG.put(l , setL);
				//System.out.println(setL);
				
				//System.out.println("hello");
			}
		}
		else if(stmt instanceof InvokeStmt) {
			//System.out.println("INVOKE STATEMENT BLOCK");
		}
		
		else if(stmt instanceof ReturnVoidStmt) {
			//System.out.println("hello");
			setOfReturns.add(unit);
		}
		else if(stmt instanceof ReturnStmt) {
			setOfReturns.add(unit);
		}
		else if(stmt instanceof IfStmt) {
			//System.out.println("INSIDE IF STATEMENT BLOCK");
		}
		else if(stmt instanceof GotoStmt) {
			//System.out.println("INSIDE GOTO STATEMENT BLOCK");
		}

//		Value lhs = ((DefinitionStmt) stmt).getLeftOp();
//		System.out.println(stackG.get(lhs.toString()));
	}
	void workListIterate(BriefUnitGraph cfg,Set<Unit> workList,Map<Unit,Map<String,Set<String>>> stack,Map<Unit,Map<Pair<String,String>,Set<String>>> heap) {
		List<Unit> headL =  cfg.getHeads();
		Set<Unit> heads = new HashSet<>();
		for(Unit head:headL)
			heads.add(head);
		
//		
//		System.out.println(heads);
//		System.out.println(workList.size());
		
		
		
		while(workList.size() != 0) {
			Unit currUnit = workList.iterator().next();
			//System.out.println("currentUnit = " + currUnit);
			workList.remove(currUnit);
			Stmt currstmt = (Stmt)currUnit;
			if(currstmt instanceof InvokeStmt || currstmt instanceof DefinitionStmt || currstmt instanceof ReturnVoidStmt || currstmt instanceof ReturnStmt || currstmt instanceof GotoStmt|| currstmt instanceof IfStmt) {
				//System.out.println("current statement = " + currstmt);
				Map<String,Set<String>> oldstackOfCurr = stack.get(currUnit);
				Map<Pair<String,String>,Set<String>> oldheapOfCurr = heap.get(currUnit);
				Map<String,Set<String>> newstackOfCurr = new HashMap<>();
				Map<Pair<String,String>,Set<String>> newheapOfCurr = new HashMap<>();

				

				List<Unit> predsList = cfg.getPredsOf(currUnit);
				
				
				for(Unit predOfUnit:predsList) {
					//if(heads.contains(predOfUnit)) continue;
					//System.out.println("INSIDE THE LOOP 1");
					Stmt predstmt = (Stmt)predOfUnit;
					if(predstmt instanceof DefinitionStmt || predstmt instanceof InvokeStmt || predstmt instanceof ReturnVoidStmt || predstmt instanceof ReturnStmt|| predstmt instanceof GotoStmt|| predstmt instanceof IfStmt) {
						//System.out.println("INSIDE THE FIRST IF AND THE PRED IS =  " + predstmt);
						Map<String,Set<String>> stackOfPred = stack.get(predOfUnit);
						Map<Pair<String,String>,Set<String>> heapOfPred = heap.get(predOfUnit);
						
						//stack join
						for(Map.Entry<String,Set<String>> entry:stackOfPred.entrySet()) {
							String predkey = entry.getKey();
							Set<String> predset = entry.getValue();
							if(predset.size() == 1 && predset.iterator().next().equals("bottom")) {
								Set<String> newset = new HashSet<>();
								newset.add("bottom");
								newstackOfCurr.put(predkey, newset);
							}
							else if(newstackOfCurr.containsKey(predkey)) {
								Set<String> newset = newstackOfCurr.get(predkey);
								if(newset.size() > 1 || !newset.iterator().next().equals("bottom")) {
									newset = Sets.union(newset, predset);
									newstackOfCurr.put(predkey, newset);
								}
							}
							else {
								Set<String> newset = new HashSet<>();
								newset.addAll(predset);
								newstackOfCurr.put(predkey, newset);
							}
						}
						
						//heap join
						for(Map.Entry<Pair<String,String>,Set<String>> entry:heapOfPred.entrySet()) {
							Pair<String,String> predkey = entry.getKey();
							Set<String> predset = entry.getValue();
							if(predset.size() == 1 && predset.iterator().next().equals("bottom")){
								Set<String> newset = new HashSet<>();
								newset.add("bottom");
								newheapOfCurr.put(predkey, newset);
							}
							else if(newheapOfCurr.containsKey(predkey)) {
								Set<String> newset = newheapOfCurr.get(predkey);
								if(newset.size() > 1 || !newset.iterator().next().equals("bottom")) {
									newset = Sets.union(newset, predset);
									newheapOfCurr.put(predkey, newset);
								}
							}
							else {
								Set<String> newset = new HashSet<>();
								newset.addAll(predset);
								newheapOfCurr.put(predkey, newset);
							}
							
						}

					}
				}
				stackG = newstackOfCurr;
				heapG = newheapOfCurr;
				Flow(currUnit);
				newstackOfCurr = stackG;
				newheapOfCurr = heapG;
				//System.out.println("AFTER FLOW  = ");
				for(Map.Entry<String, Set<String>> entry1:newstackOfCurr.entrySet()) {
					//System.out.println(entry1.getKey() + "    " + entry1.getValue());
				}
			
				if(!newstackOfCurr.equals(oldstackOfCurr) || !newheapOfCurr.equals(oldheapOfCurr)) {
					stack.put(currUnit, newstackOfCurr);
					heap.put(currUnit, newheapOfCurr);
					workList.addAll(cfg.getSuccsOf(currUnit));
				}
				//System.out.println("WORKLIST = " + workList);
			}
		}
		
		
		
	}
		

	
	protected synchronized void internalTransform(Body arg0, String arg1, Map<String, String> arg2) {
		//System.out.println("****************************************");
		stackG = null;
		heapG = null;
		finalstackG = new HashMap<>();;
		finalheapG = new HashMap<>();
		visitedNewStmt = null;
		objType = null;
		count = 1;
		setOfReturns = new HashSet<>();
		//adding the formal parameters of the method to this formalParams list
		formalParams = new HashSet<>();
		
		
		//getting the locals , it does not include "this" pointer
		List<Local> listOfParams = arg0.getParameterLocals();

		for(Local l:listOfParams) {
			
			if(l.getType() instanceof RefLikeType) {
				formalParams.add(l.toString());
			}
		}
		
		
		
		
		
		
		Chain<SootField> AllFields = arg0.getMethod().getDeclaringClass().getFields();
//		for(SootField f:AllFields) {
//			System.out.println("SSS" + f);
//		}
		objType = new HashMap<>();
		//System.out.println(AllFields.size());
		String methodName = arg0.getMethod().getName();
		String className = arg0.getMethod().getDeclaringClass().toString();
		//System.out.println(methodName + " "+ className);
		visitedNewStmt = new HashMap<>();
		
		BriefUnitGraph cfg = new BriefUnitGraph(arg0); 
		
		Chain<Local> locals = arg0.getLocals();

		PatchingChain<Unit> AllUnits = arg0.getUnits();
		
		Set<Unit> workList = new HashSet<Unit>();
		for(Unit unit:AllUnits) {
			workList.add(unit);
		}
		workList.removeAll(cfg.getHeads());
		
		List<Unit> headL =  cfg.getHeads();
		Set<Unit> heads = new HashSet<>();
		for(Unit head:headL)
			heads.add(head);
		
		/////////////////////////////////////////////////////////////////////////
		
		Map<Unit,Map<String,Set<String>>> stack = new HashMap<>();
		Map<Unit,Map<Pair<String,String>,Set<String>>> heap = new HashMap<>();
		/////////////////////////////////////////////////////////////////////////
		
		
		
		
		
		for(Unit currUnit:AllUnits) {
			Map<String,Set<String>> map1 = new HashMap<>();
			Map<Pair<String,String>,Set<String>> map2 = new HashMap<>();

			if(heads.contains(currUnit)) {
				Stmt stmt = (Stmt)currUnit;
				if(stmt instanceof DefinitionStmt) {
					//System.out.println("INSIDE THE DEFINITION STMT BLOCK");
					Value lhs = ((DefinitionStmt) stmt).getLeftOp();
					Value rhs = ((DefinitionStmt) stmt).getRightOp();
					String l = lhs.toString();
					Set<String> set = new HashSet<>();
					String obj = "bottom";
					//objType.put(obj, rhs.getType());
		
					set.add(obj);
					map1.put(l,set);
				}
			}
			
			for(String param:formalParams) {
				Set<String> set = new HashSet<>();
				set.add("bottom");
				map1.put(param, set);
			}
			
			
			stack.put(currUnit, map1);
			heap.put(currUnit, map2);
		}
		

		
		/////////////////////////////////////////////////////////////////////////
		
		///////////////////////////////////////////////////////////////////////

		workListIterate(cfg,workList,stack,heap);
		

		for(Unit unit:setOfReturns) {
			stackG = stack.get(unit);
			heapG = heap.get(unit);
			//System.out.println(stackG.size());
			//System.out.println(heapG.size());
			//System.out.println("IN RETURN BLOCK");
			for(Map.Entry<String, Set<String>> entry:stackG.entrySet()) {
				String key = entry.getKey();
				Set<String> set = entry.getValue();
				if(set.size() == 1 && set.iterator().next().equals("bottom")) {
					Set<String> newset = new HashSet<>();
					newset.add("bottom");
					finalstackG.put(key, newset);
				}
				else if(finalstackG.containsKey(key)) {
					Set<String> newset = finalstackG.get(key);
					if(newset.size() != 1 || !newset.iterator().next().equals("bottom")) {
						newset = Sets.union(newset, set);
						finalstackG.put(key, newset);
					}
				}
				else {
					Set<String> newset = new HashSet<>();
					newset.addAll(set);
					finalstackG.put(key, newset);
				}
			}
			for(Map.Entry<Pair<String,String>,Set<String>> entry:heapG.entrySet()) {
				Pair<String,String> key = entry.getKey();
				Set<String> set = entry.getValue();
				if(set.size() == 1 && set.iterator().next().equals("bottom")){
					Set<String> newset = new HashSet<>();
					newset.add("bottom");
					finalheapG.put(key, newset);
				}
				else if(finalheapG.containsKey(key)) {
					Set<String> newset = finalheapG.get(key);
					if(newset.size() != 1 || !newset.iterator().next().equals("bottom")) {
						newset = Sets.union(newset, set);
						finalheapG.put(key, newset);
					}
				}
				else {
					Set<String> newset = new HashSet<>();
					newset.addAll(set);
					finalheapG.put(key, newset);
				}
			}
		}
		
		
		
		
		//return stack (or) finalstackG print
		//System.out.println("FINAL ANS STACK");
		for(Map.Entry<String, Set<String>> entry1:finalstackG.entrySet()) {
			//System.out.println(entry1.getKey() + "    " + entry1.getValue());
		}

		//System.out.println("FINAL ANS HEAP");
		for(Map.Entry<Pair<String,String>,Set<String>> entry1:finalheapG.entrySet()) {
			//System.out.print("FIELD NAME = " + entry1.getKey());
			//System.out.println("   => " + entry1.getValue());
		}
		
		//System.out.println("_______________________________");
		//System.out.println(A1.queryList.size());
		//System.out.println(A1.answers.length);
		for(int i = 0;i < A1.queryList.size();i ++) {
			AliasQuery q = A1.queryList.get(i);
			String queryClassName = q.getClassName();
			String queryMethodName = q.getMethodName();
			String queryLeftVar = q.getLeftVar();
			String queryRightVar = q.getRightVar();
			//System.out.println(queryClassName);
			//System.out.println(queryMethodName);
			
			if(!queryClassName.equals(className) || !queryMethodName.equals(methodName)) {
				continue;
			}
			
			//System.out.println(queryClassName);
			//System.out.println(queryMethodName);
			if(!finalstackG.containsKey(queryLeftVar) || !finalstackG.containsKey(queryRightVar)) {
				A1.answers[i] = "No";
				continue;
			}
			Set<String> set1 = finalstackG.get(queryLeftVar);
			Set<String> set2 = finalstackG.get(queryRightVar);
			//System.out.println(queryLeftVar);
			//System.out.println(queryRightVar);

			if(set1.size() == 1 && set1.iterator().next().equals("bottom")) {
				A1.answers[i] = "Yes";
			}
			else if(set2.size() == 1 && set2.iterator().next().equals("bottom")) {
				A1.answers[i] = "Yes";
			}
			else {
				Set<String> res = Sets.intersection(set1, set2);
				if(res.size() > 0) {
					A1.answers[i] = "Yes";
				}
				else {
					A1.answers[i] = "No";
				}
			}
			
			
			
		}
		
		
		//System.out.println("END");
	}
	
}