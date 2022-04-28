#!/usr/bin/python3.9
import matplotlib.pyplot as plt
import networkx as nx
import subprocess
import json
from pprint import pp

srcFilename = "./example.cc"
varToTrace = "X"

class Variable:
    allVars = {}
    varToTraceId = None

    def __init__(self, id, name):
        self.id   = id
        self.name = name

        # Keep track of all variables
        Variable.allVars[id] = name
        if self.name == varToTrace and Variable.varToTraceId is None:
            Variable.varToTraceId = self.id
    def __str__(self):
        return self.name + "." + self.id

class VariableAssignment:
    allAssignments = {}
    allAssignmentsByName = {} # For debugging

    def __init__(self, id, values):
        self.id = id
        self.left = values[0]
        self.right = values[1:]
        if self.left is not None:
            VariableAssignment.allAssignments[self.id] = (self.left.id, [v.id if v is not None else None for v in self.right])
            VariableAssignment.allAssignmentsByName[self.id] = (self.left.name, [str(v.name) if v is not None else None for v in self.right])
            

class FunctionDeclaration:
    allFuncDeclarations = {}
    allFuncDeclByName = {}
    memcpyId = None
    freeId = None

    def __init__(self, id, name, params):
        self.id     = id
        self.name   = name
        self.params = params
        FunctionDeclaration.allFuncDeclarations[self.id] = [p.id for p in self.params if p is not None]
        FunctionDeclaration.allFuncDeclByName[self.id] = (self.name, [p.name for p in self.params if p is not None ])

        # Check if this is the declaration of memcpy
        if self.name == "memcpy":
            FunctionDeclaration.memcpyId = self.id
        if self.name == "free":
            FunctionDeclaration.freeId = self.id

    def __str__(self):
        return self.name + "." + self.id + "(" + ','.join([p.name + "." + p.id if p is not None else None for p in self.params]) + ")"

class FunctionCall:
    allFuncCalls = {}

    def __init__(self, id, calledFuncId, params):
        self.id = id
        self.calledFuncId = calledFuncId
        self.params = params
        FunctionCall.allFuncCalls[self.id] = (self.calledFuncId, [p.id if p is not None else None for p in self.params])

class AstNode:
    allNodes = {}
    currentFile = None

    def __init__(self, root, parent):
        self.root = root
        self.id = self.getField("id")
        if self.id is not None:
            AstNode.allNodes[self.id] = self
        self.parent = parent
        self.file = None
        self.loc = self.objectFromField(LocField, "loc")
        if self.loc is not None:
            self.file = self.loc.getField("file")
        if self.file is None:
            self.file = AstNode.currentFile
        else:
            AstNode.currentFile = self.file

        self.kind = self.getField("kind")
        self.inner = []
        self.variables = None
        self.parameters = None
        self.arguments = None
        self.analyzeChildren()

    def getField(self, field):
        return self.root[field] if field in self.root else None

    def objectFromField(self, obj, field):
        return obj(self.root[field], self) if field in self.root else None

    def analyzeChildren(self):
        if "inner" in self.root:
            for childNode in self.root["inner"]:
                if len(childNode) == 0:
                    continue
                self.inner.append(nodeKindMap[childNode["kind"]](childNode, self))

    def checkAttributeCoverage(self):
        # For debugging... can pick out if we've missed any attributes
        # in the AST for any particular node.
        attributes = self.__dict__.keys()
        supplied   = self.root.keys()
        diff = supplied - attributes
        if len(diff) != 0:
            print("Found unexpected parameters in the AST for nodes of kind " + str(self.kind) + ":")
            for d in diff:
                pp((d, self.root[d]))

    def printMe(self, toDepth=1, printHash = True, printVars = True):
        if printHash:
            pp(self.root, depth=toDepth)
        if printVars:
            for key, value in self.__dict__.items():
                if key == "root" or key == "parent":
                    continue
                print(key + " = \"" + str(value) + "\"")

    def findVariables(self):
        if self.variables is None:
            self.variables = []
            if len(self.inner) > 0:
                for child in self.inner:
                    self.variables.extend(child.findVariables())
            else:
                self.variables = [None]
        return self.variables

    def findParameters(self): 
        if self.parameters is None:
            self.parameters = []
            if len(self.inner) > 0:
                for child in self.inner:
                    self.parameters.extend(child.findParameters())
            else:
                self.parameters = [None]
        return self.parameters

    def findArguments(self):
        if self.arguments is None:
            self.arguments = []
            if len(self.inner) > 0:
                for child in self.inner:
                    self.arguments.extend(child.findArguments())
            else:
                self.arguments = [None]
        return self.arguments

    def findCalledFunc(self): 
        if len(self.inner) > 0:
            for child in self.inner:
                return child.findCalledFunc()
        else:
            return (None, None)
            
class AnyInitField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.name = self.getField("name")
        self.type        = self.objectFromField(TypeField, "type")
        self.checkAttributeCoverage()
        
class BeginField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.offset = self.getField("offset")
        self.col    = self.getField("col")
        self.tokLen = self.getField("tokLen")
        self.includedFrom = self.objectFromField(IncludedFromField, "includedFrom")
        self.spellingLoc = self.objectFromField(SpellingLocField, "spellingLoc")
        self.expansionLoc = self.objectFromField(ExpansionLocField, "expansionLoc")
        self.line = self.getField("line")
        self.checkAttributeCoverage()

class CopyAssignField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.hasConstParam         = self.getField("hasConstParam")
        self.implicitHasConstParam = self.getField("implicitHasConstParam")
        self.needsImplicit         = self.getField("needsImplicit")
        self.simple                = self.getField("simple")
        self.trivial               = self.getField("trivial")
        self.checkAttributeCoverage()

class CopyCtorField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.hasConstParam         = self.getField("hasConstParam")
        self.implicitHasConstParam = self.getField("implicitHasConstParam")
        self.needsImplicit         = self.getField("needsImplicit")
        self.simple                = self.getField("simple")
        self.trivial               = self.getField("trivial")
        self.checkAttributeCoverage()
        
class DeclField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.name        = self.getField("name")
        self.checkAttributeCoverage()

class DefaultCtorField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.exists        = self.getField("exists")
        self.needsImplicit = self.getField("needsImplicit")
        self.trivial       = self.getField("trivial")
        self.checkAttributeCoverage()

class DefinitionDataField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.canPassInRegisters  = self.getField("canPassInRegisters")
        self.copyAssign          = self.objectFromField(CopyAssignField, "copyAssign")
        self.copyCtor            = self.objectFromField(CopyCtorField, "copyCtor")
        self.defaultCtor         = self.objectFromField(DefaultCtorField, "defaultCtor")
        self.dtor                = self.objectFromField(DtorField, "dtor")
        self.hasVariantMembers   = self.getField("hasVariantMembers")
        self.isAggregate         = self.getField("isAggregate")
        self.isLiteral           = self.getField("isLiteral")
        self.isPOD               = self.getField("isPOD")
        self.isStandardLayout    = self.getField("isStandardLayout")
        self.isTrivial           = self.getField("isTrivial")
        self.isTriviallyCopyable = self.getField("isTriviallyCopyable")
        self.moveAssign          = self.objectFromField(MoveAssignField, "moveAssign")
        self.moveCtor            = self.objectFromField(MoveCtorField, "moveCtor")
        self.checkAttributeCoverage()

class DtorField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.irrelevant    = self.getField("irrelevant")
        self.needsImplicit = self.getField("needsImplicit")
        self.simple        = self.getField("simple")
        self.trivial       = self.getField("trivial")
        self.checkAttributeCoverage()

class EndField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.offset = self.getField("offset")
        self.line   = self.getField("line")
        self.col    = self.getField("col")
        self.tokLen = self.getField("tokLen")
        self.includedFrom = self.objectFromField(IncludedFromField, "includedFrom")
        self.spellingLoc = self.objectFromField(SpellingLocField, "spellingLoc")
        self.expansionLoc = self.objectFromField(ExpansionLocField, "expansionLoc")
        self.checkAttributeCoverage()

class ExpansionLocField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.offset = self.getField("offset")
        self.file = self.getField("file")
        self.line   = self.getField("line")
        self.col    = self.getField("col")
        self.tokLen = self.getField("tokLen")
        self.includedFrom = self.objectFromField(IncludedFromField, "includedFrom")
        self.isMacroArgExpansion = self.getField("isMacroArgExpansion")
        self.checkAttributeCoverage()

class IncludedFromField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.file = self.getField("file")
        
class LocField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.offset = self.getField("offset")
        self.line   = self.getField("line")
        self.col    = self.getField("col")
        self.tokLen = self.getField("tokLen")
        self.file = self.getField("file")
        self.includedFrom = self.objectFromField(IncludedFromField, "includedFrom")
        self.spellingLoc = self.objectFromField(SpellingLocField, "spellingLoc")
        self.expansionLoc = self.objectFromField(ExpansionLocField, "expansionLoc")
        self.checkAttributeCoverage()

class MoveAssignField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.exists        = self.getField("exists")
        self.needsImplicit = self.getField("needsImplicit")
        self.simple        = self.getField("simple")
        self.trivial       = self.getField("trivial")
        self.checkAttributeCoverage()

class MoveCtorField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.exists        = self.getField("exists")
        self.needsImplicit = self.getField("needsImplicit")
        self.simple        = self.getField("simple")
        self.trivial       = self.getField("trivial")
        self.checkAttributeCoverage()

class OriginalNamespaceField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.name        = self.getField("name")
        self.checkAttributeCoverage()

class OwnedTagDeclField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.name          = self.getField("name")
        self.checkAttributeCoverage()
                
class RangeField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.begin = self.objectFromField(BeginField, "begin")
        self.end = self.objectFromField(EndField, "end")
        self.checkAttributeCoverage()

class SpellingLocField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.offset = self.getField("offset")
        self.file = self.getField("file")
        self.line   = self.getField("line")
        self.col    = self.getField("col")
        self.tokLen = self.getField("tokLen")
        self.includedFrom = self.objectFromField(IncludedFromField, "includedFrom")
        self.presumedLine = self.getField("presumedLine")
        self.checkAttributeCoverage()

class TargetField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.name        = self.getField("name")
        self.type        = self.objectFromField(TypeField, "type")
        self.checkAttributeCoverage()

class TypeField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.qualType = self.getField("qualType")
        self.desugaredQualType = self.getField("desugaredQualType")
        self.typeAliasDeclId = self.getField("typeAliasDeclId")
        self.checkAttributeCoverage()

################################################################################
# Nodes - These will show up in an "inner" field
################################################################################

class AbiTagAttrNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.checkAttributeCoverage()

class ArgTypeField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.qualType = self.getField("qualType")
        self.checkAttributeCoverage()

class ArraySubscriptExprNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range         = self.objectFromField(RangeField, "range")  
        self.type          = self.objectFromField(TypeField, "type")
        self.valueCategory = self.getField("valueCategory")
        self.checkAttributeCoverage()

class AsmLabelAttrNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.checkAttributeCoverage()

class BinaryOperatorNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range         = self.objectFromField(RangeField, "range")
        self.type          = self.objectFromField(TypeField, "type")
        self.valueCategory = self.getField("valueCategory")
        self.opcode        = self.getField("opcode")

        if self.opcode == "=":
            # This is an assignment operator, find the variables on either side of the equation
            self.findVariables()
            self.assignment = VariableAssignment(self.id, self.variables)
        self.checkAttributeCoverage()

    def findVariables(self):
        if self.variables is None:
            super().findVariables()
        if self.opcode == "=":
            # If this is an assignment, only return the lvalue
            return [self.variables[0]]
        else:
            self.variables = [v for v in self.variables if v is not None]
            return self.variables

class BreakStmtNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range = self.objectFromField(RangeField, "range")
        self.checkAttributeCoverage()

class BuiltinAttrNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.implicit    = self.getField("implicit")
        self.inherited    = self.getField("inherited")
        self.checkAttributeCoverage()

class BuiltinTypeNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.type = self.objectFromField(TypeField, "type")
        self.checkAttributeCoverage()

class CallExprNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.type        = self.objectFromField(TypeField, "type")
        self.valueCategory = self.getField("valueCategory")
        self.calledFuncId = None
        self.calledFuncName = None
        self.arguments = None
        self.checkAttributeCoverage()
        self.findCalledFunc()
        if self.calledFuncId is not None and self.calledFuncName is not None:
            self.findArguments()
            self.functionCall = FunctionCall(self.id, self.calledFuncId, self.arguments)
        
    def findVariables(self):
        ## TODO Can a data dependency by established with the return value?
        return [None]
    
    def findCalledFunc(self):
        for child in self.inner:
            if self.calledFuncId is not None:
                break
            self.calledFuncId, self.calledFuncName = child.findCalledFunc()

    def findArguments(self):
        self.arguments = []
        for child in self.inner:
            self.arguments.extend(child.findArguments())
        return self.arguments
        

class CaseStmtNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range = self.objectFromField(RangeField, "range") 
        self.checkAttributeCoverage()

class CharacterLiteralNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range         = self.objectFromField(RangeField, "range")  
        self.type          = self.objectFromField(TypeField, "type")
        self.valueCategory = self.getField("valueCategory")
        self.value         = self.getField("value")
        self.checkAttributeCoverage()
        
class CompoundStmtNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range = self.objectFromField(RangeField, "range")
        self.checkAttributeCoverage()

class ConditionalOperatorNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range         = self.objectFromField(RangeField, "range")
        self.type          = self.objectFromField(TypeField, "type")
        self.valueCategory = self.getField("valueCategory")
        self.checkAttributeCoverage()

        
class ConstantArrayTypeNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.type        = self.objectFromField(TypeField, "type")
        self.size          = self.getField("size")
        self.checkAttributeCoverage()

class ConstantExprNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range         = self.objectFromField(RangeField, "range")
        self.type          = self.objectFromField(TypeField, "type")
        self.valueCategory = self.getField("valueCategory")
        self.value         = self.getField("value")
        self.checkAttributeCoverage()

class ConstAttrNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.implicit          = self.getField("implicit")
        self.checkAttributeCoverage()

class CStyleCastExprNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.type        = self.objectFromField(TypeField, "type")
        self.valueCategory = self.getField("valueCategory")
        self.castKind = self.getField("castKind")
        self.checkAttributeCoverage()

class CtorTypeField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.qualType = self.getField("qualType")
        self.checkAttributeCoverage()

class CXXConstructExprNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range                 = self.objectFromField(RangeField, "range")
        self.type                  = self.objectFromField(TypeField, "type")
        self.valueCategory         = self.getField("valueCategory")
        self.ctorType              = self.objectFromField(CtorTypeField, "ctorType")
        self.elidable              = self.getField("elidable")
        self.hadMultipleCandidates = self.getField("hadMultipleCandidates")
        self.constructionKind      = self.getField("constructionKind")
        self.checkAttributeCoverage()

class CXXConstructorDeclNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.loc         = self.objectFromField(LocField, "loc")
        self.range       = self.objectFromField(RangeField, "range")
        self.isImplicit  = self.getField("isImplicit")
        self.name = self.getField("name")
        self.mangledName = self.getField("mangledName")
        self.type        = self.objectFromField(TypeField, "type")
        self.inline = self.getField("inline")
        self.constexpr = self.getField("constexpr")
        self.isUsed = self.getField("isUsed")
        self.explicitlyDefaulted = self.getField("explicitlyDefaulted")
        self.checkAttributeCoverage()

class CXXCtorInitializerNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.anyInit = self.objectFromField(AnyInitField, "anyInit")
        self.checkAttributeCoverage()  
        
class CXXDestructorDeclNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.loc         = self.objectFromField(LocField, "loc")
        self.range       = self.objectFromField(RangeField, "range")
        self.isImplicit  = self.getField("isImplicit")
        self.isReferenced  = self.getField("isReferenced")
        self.name = self.getField("name")
        self.mangledName = self.getField("mangledName")
        self.type        = self.objectFromField(TypeField, "type")
        self.inline = self.getField("inline")
        self.explicitlyDefaulted = self.getField("explicitlyDefaulted")
        self.checkAttributeCoverage()

class CXXNullPtrLiteralExprNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.type        = self.objectFromField(TypeField, "type")
        self.valueCategory = self.getField("valueCategory")
        self.checkAttributeCoverage()

class CXXRecordDeclNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.loc         = self.objectFromField(LocField, "loc")
        self.range       = self.objectFromField(RangeField, "range")
        self.tagUsed     = self.getField("tagUsed")
        self.name     = self.getField("name")
        self.isImplicit     = self.getField("isImplicit")
        self.previousDecl     = self.getField("previousDecl")
        self.parentDeclContextId     = self.getField("parentDeclContextId")
        self.completeDefinition = self.getField("completeDefinition")
        self.definitionData = self.objectFromField(DefinitionDataField, "definitionData")
        self.checkAttributeCoverage()

class CXXStaticCastExprNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.type        = self.objectFromField(TypeField, "type")
        self.valueCategory = self.getField("valueCategory")
        self.castKind = self.getField("castKind")
        self.checkAttributeCoverage()

class DeclRefExprNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.type        = self.objectFromField(TypeField, "type")
        self.valueCategory = self.getField("valueCategory")
        self.referencedDecl = self.objectFromField(ReferencedDeclNode, "referencedDecl")
        self.foundReferencedDecl = self.objectFromField(FoundReferencedDeclField, "foundReferencedDecl")
        self.checkAttributeCoverage()

    def findVariables(self):
        if self.referencedDecl.kind == "VarDecl":
            varId   = self.referencedDecl.id
            varName = self.referencedDecl.name
            return [Variable(varId, varName)]
        else:
            # TODO: Figure out other kinds of assignments
            return [None]

    def findCalledFunc(self):
        if self.referencedDecl.kind == "FunctionDecl":
            return (self.referencedDecl.id, self.referencedDecl.name)
        else:
            return (None, None)

    def findArguments(self):
        if self.referencedDecl.kind in ["VarDecl", "ParmVarDecl"]:
            argId   = self.referencedDecl.id
            argName = self.referencedDecl.name
            return [Variable(argId, argName)]
        else:
            # TODO: Figure out other kinds of arguments
            return []

class DeclStmtNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range = self.objectFromField(RangeField, "range")
        self.checkAttributeCoverage()

class DecltypeTypeNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.type        = self.objectFromField(TypeField, "type")
        self.checkAttributeCoverage()

class DefaultStmtNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range = self.objectFromField(RangeField, "range")
        self.checkAttributeCoverage()

class DoStmtNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range = self.objectFromField(RangeField, "range")

class ElaboratedTypeNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.type        = self.objectFromField(TypeField, "type")
        self.ownedTagDecl = self.objectFromField(OwnedTagDeclField, "ownedTagDecl")
        self.checkAttributeCoverage()

class ExprWithCleanupsNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range         = self.objectFromField(RangeField, "range")
        self.type          = self.objectFromField(TypeField, "type")
        self.valueCategory = self.getField("valueCategory")
        self.checkAttributeCoverage()

class FieldDeclNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.loc         = self.objectFromField(LocField, "loc")
        self.range       = self.objectFromField(RangeField, "range")
        self.type        = self.objectFromField(TypeField, "type")
        self.name          = self.getField("name")
        self.isImplicit          = self.getField("isImplicit")
        self.isReferenced          = self.getField("isReferenced")
        self.checkAttributeCoverage()

class FormatAttrNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.implicit    = self.getField("implicit")
        self.inherited    = self.getField("inherited")
        self.checkAttributeCoverage()

class ForStmtNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range = self.objectFromField(RangeField, "range")   
        self.checkAttributeCoverage()

class FoundReferencedDeclField(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.name        = self.getField("name")
        self.type        = self.objectFromField(TypeField, "type")
        self.checkAttributeCoverage()

class FunctionDeclNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.loc          = self.objectFromField(LocField, "loc")
        self.range        = self.objectFromField(RangeField, "range")
        self.isUsed       = self.getField("isUsed")
        self.name         = self.getField("name")
        self.mangledName  = self.getField("mangledName")
        self.type         = self.objectFromField(TypeField, "type")
        self.storageClass = self.getField("storageClass")
        self.variadic     = self.getField("variadic")
        self.previousDecl = self.getField("previousDecl")
        self.inline       = self.getField("inline")
        self.constexpr    = self.getField("constexpr")
        self.isImplicit   = self.getField("isImplicit")
        self.params       = None
        self.findParameters()
        self.checkAttributeCoverage()

    def findParameters(self):
        self.params = []
        for child in self.inner:
            # The body of the function is a CompoundStmt, so search everything but that
            if child.kind != "CompoundStmt":
                self.params.extend(child.findParameters())
        self.functionDeclaration = FunctionDeclaration(self.id, self.name, self.params)

class FunctionPrototypeNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.type        = self.objectFromField(TypeField, "type")
        self.cc = self.getField("cc")
        self.checkAttributeCoverage()

class GNUNullExprNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range         = self.objectFromField(RangeField, "range")
        self.type          = self.objectFromField(TypeField, "type")
        self.valueCategory = self.getField("valueCategory")
        self.checkAttributeCoverage()

class IfStmtNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range   = self.objectFromField(RangeField, "range") 
        self.hasElse = self.getField("hasElse")
        self.checkAttributeCoverage()
        
class ImplicitCastExprNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range                = self.objectFromField(RangeField, "range")
        self.type                 = self.objectFromField(TypeField, "type")
        self.valueCategory        = self.getField("valueCategory")
        self.castKind             = self.getField("castKind")
        self.isPartOfExplicitCast = self.getField("isPartOfExplicitCast")
        self.checkAttributeCoverage()

class IndirectFieldDeclNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.loc         = self.objectFromField(LocField, "loc")
        self.range       = self.objectFromField(RangeField, "range")
        self.isImplicit          = self.getField("isImplicit")
        self.name          = self.getField("name")
        self.checkAttributeCoverage()

class IntegerLiteralNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.type        = self.objectFromField(TypeField, "type")
        self.valueCategory = self.getField("valueCategory")
        self.value = self.getField("value")
        self.checkAttributeCoverage()

class LinkageSpecDeclNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.loc         = self.objectFromField(LocField, "loc")
        self.range       = self.objectFromField(RangeField, "range")
        self.language    = self.getField("language")
        self.hasBraces   = self.getField("hasBraces")
        self.isImplicit  = self.getField("isImplicit")
        self.checkAttributeCoverage()

class MaterializeTemporaryExprNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.type        = self.objectFromField(TypeField, "type")
        self.valueCategory = self.getField("valueCategory")
        self.storageDuration = self.getField("storageDuration")
        self.checkAttributeCoverage()

class MemberExprNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.type        = self.objectFromField(TypeField, "type")
        self.valueCategory = self.getField("valueCategory")
        self.name = self.getField("name")
        self.isArrow = self.getField("isArrow")
        self.referencedMemberDecl = self.getField("referencedMemberDecl")
        self.checkAttributeCoverage()
    
class ModeAttrNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.checkAttributeCoverage()

class NamespaceDeclNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.loc               = self.objectFromField(LocField, "loc")
        self.range             = self.objectFromField(RangeField, "range")
        self.name              = self.getField("name")
        self.isInline          = self.getField("isInline")
        self.previousDecl      = self.getField("previousDecl")
        self.originalNamespace = self.objectFromField(OriginalNamespaceField, "originalNamespace")
        self.checkAttributeCoverage()

class NonNullAttrNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.checkAttributeCoverage()
          
class NoThrowAttrNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.implicit          = self.getField("implicit")
        self.checkAttributeCoverage()

class ParenExprNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.type        = self.objectFromField(TypeField, "type")
        self.valueCategory = self.getField("valueCategory")
        self.checkAttributeCoverage()

class ParenTypeNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.type        = self.objectFromField(TypeField, "type")
        self.checkAttributeCoverage()

class ParmValDeclNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.loc         = self.objectFromField(LocField, "loc")
        self.range       = self.objectFromField(RangeField, "range")
        self.isUsed      = self.getField("isUsed")
        self.name        = self.getField("name")
        self.mangledName = self.getField("mangledName")
        self.type        = self.objectFromField(TypeField, "type")
        self.checkAttributeCoverage()
    def findParameters(self):
        return [Variable(self.id, self.name)]

class PointerTypeNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.type        = self.objectFromField(TypeField, "type")
        self.checkAttributeCoverage()

class PureAttrNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.checkAttributeCoverage()

class QualTypeNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.type        = self.objectFromField(TypeField, "type")
        self.qualifiers = self.getField("qualifiers")
        self.checkAttributeCoverage()

class RecordTypeNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.type        = self.objectFromField(TypeField, "type")
        self.decl        = self.objectFromField(DeclField, "decl")
        self.checkAttributeCoverage()

class ReferencedDeclNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.name        = self.getField("name")
        self.type        = self.objectFromField(TypeField, "type")
        self.checkAttributeCoverage()

class RestrictAttrNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.checkAttributeCoverage()

class ReturnStmtNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range = self.objectFromField(RangeField, "range")
        self.checkAttributeCoverage()


class StringLiteralNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range         = self.objectFromField(RangeField, "range")  
        self.type          = self.objectFromField(TypeField, "type")
        self.valueCategory = self.getField("valueCategory")
        self.value         = self.getField("value")
        self.checkAttributeCoverage()

class SwitchStmtNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range         = self.objectFromField(RangeField, "range") 
        self.checkAttributeCoverage()

class TranslationUnitDeclNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.loc         = self.objectFromField(LocField, "loc")
        self.range       = self.objectFromField(RangeField, "range")
        self.checkAttributeCoverage()

class TypedefDeclNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.loc         = self.objectFromField(LocField, "loc")
        self.range       = self.objectFromField(RangeField, "range")
        self.isImplicit  = self.getField("isImplicit")
        self.isReferenced  = self.getField("isReferenced")
        self.previousDecl  = self.getField("previousDecl")
        self.name        = self.getField("name")
        self.type        = self.objectFromField(TypeField, "type")
        self.checkAttributeCoverage()

class TypedefTypeNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.type        = self.objectFromField(TypeField, "type")
        self.decl        = self.objectFromField(DeclField, "decl")
        self.checkAttributeCoverage()

class UnaryExprOrTypeTraitExprNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range         = self.objectFromField(RangeField, "range")  
        self.type          = self.objectFromField(TypeField, "type")
        self.valueCategory = self.getField("valueCategory")
        self.name         = self.getField("name")
        self.argType   = self.objectFromField(ArgTypeField, "argType")
        self.checkAttributeCoverage()

class UnaryOperatorNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range         = self.objectFromField(RangeField, "range")
        self.type          = self.objectFromField(TypeField, "type")
        self.valueCategory = self.getField("valueCategory")
        self.isPostfix     = self.getField("isPostfix")
        self.opcode        = self.getField("opcode")
        self.checkAttributeCoverage()

class UsingDeclNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.loc         = self.objectFromField(LocField, "loc")
        self.range       = self.objectFromField(RangeField, "range")
        self.name        = self.getField("name")
        self.checkAttributeCoverage()

class UsingShadowDeclNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.loc         = self.objectFromField(LocField, "loc")
        self.range       = self.objectFromField(RangeField, "range")
        self.isImplicit  = self.getField("isImplicit")
        self.target      = self.objectFromField(TargetField, "target")
        self.checkAttributeCoverage()

class VarDeclNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.loc         = self.objectFromField(LocField, "loc")
        self.range       = self.objectFromField(RangeField, "range")
        self.isUsed      = self.getField("isUsed")
        self.name        = self.getField("name")
        self.nrvo        = self.getField("nrvo")
        self.init        = self.getField("init")
        self.mangledName = self.getField("mangledName")
        self.type        = self.objectFromField(TypeField, "type")
        self.storageClass = self.getField("storageClass")
        self.findVariables()
        self.checkAttributeCoverage()

    def findVariables(self):
        self.variables = [Variable(self.id, self.name)]
        for child in self.inner:
            self.variables.extend(child.findVariables())
        if len(self.variables) > 1:
            self.assignment = VariableAssignment(self.id, self.variables)

class VisibilityAttrNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.checkAttributeCoverage()

class WarnUnusedResultAttrNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range       = self.objectFromField(RangeField, "range")
        self.inherited          = self.getField("inherited")
        self.checkAttributeCoverage()

class WhileStmtNode(AstNode):
    def __init__(self, root, parent):
        super().__init__(root, parent)
        self.range = self.objectFromField(RangeField, "range")  
        self.checkAttributeCoverage()

nodeKindMap = {
    "AbiTagAttr"               : AbiTagAttrNode,
    "ArraySubscriptExpr"       : ArraySubscriptExprNode,
    "AsmLabelAttr"             : AsmLabelAttrNode,
    "BinaryOperator"           : BinaryOperatorNode,
    "BreakStmt"                : BreakStmtNode,
    "BuiltinAttr"              : BuiltinAttrNode,
    "BuiltinType"              : BuiltinTypeNode,
    "CallExpr"                 : CallExprNode,
    "CaseStmt"                 : CaseStmtNode,
    "CharacterLiteral"         : CharacterLiteralNode,
    "CompoundStmt"             : CompoundStmtNode,
    "ConditionalOperator"      : ConditionalOperatorNode,
    "ConstantArrayType"        : ConstantArrayTypeNode,
    "ConstAttr"                : ConstAttrNode,
    "ConstantExpr"             : ConstantExprNode,
    "CStyleCastExpr"           : CStyleCastExprNode,
    "CXXConstructExpr"         : CXXConstructExprNode,
    "CXXConstructorDecl"       : CXXConstructorDeclNode,
    "CXXCtorInitializer"       : CXXCtorInitializerNode,
    "CXXDestructorDecl"        : CXXDestructorDeclNode,
    "CXXNullPtrLiteralExpr"    : CXXNullPtrLiteralExprNode,
    "CXXRecordDecl"            : CXXRecordDeclNode,
    "CXXStaticCastExpr"        : CXXStaticCastExprNode,
    "DeclRefExpr"              : DeclRefExprNode,
    "DeclStmt"                 : DeclStmtNode,
    "DecltypeType"             : DecltypeTypeNode,
    "DefaultStmt"              : DefaultStmtNode,
    "DoStmt"                   : DoStmtNode,
    "ElaboratedType"           : ElaboratedTypeNode,
    "ExprWithCleanups"         : ExprWithCleanupsNode,
    "FieldDecl"                : FieldDeclNode,
    "FormatAttr"               : FormatAttrNode,
    "ForStmt"                  : ForStmtNode,
    "FunctionDecl"             : FunctionDeclNode,
    "FunctionProtoType"        : FunctionPrototypeNode,
    "GNUNullExpr"              : GNUNullExprNode,
    "IfStmt"                   : IfStmtNode,
    "ImplicitCastExpr"         : ImplicitCastExprNode,
    "IndirectFieldDecl"        : IndirectFieldDeclNode,
    "IntegerLiteral"           : IntegerLiteralNode,
    "LinkageSpecDecl"          : LinkageSpecDeclNode,
    "MaterializeTemporaryExpr" : MaterializeTemporaryExprNode,
    "MemberExpr"               : MemberExprNode,
    "ModeAttr"                 : ModeAttrNode,
    "NamespaceDecl"            : NamespaceDeclNode,
    "NonNullAttr"              : NonNullAttrNode,
    "NoThrowAttr"              : NoThrowAttrNode,
    "ParenExpr"                : ParenExprNode,
    "ParenType"                : ParenTypeNode,
    "ParmVarDecl"              : ParmValDeclNode,
    "PointerType"              : PointerTypeNode,
    "PureAttr"                 : PureAttrNode,
    "QualType"                 : QualTypeNode,
    "RecordType"               : RecordTypeNode,
    "RestrictAttr"             : RestrictAttrNode,
    "ReturnStmt"               : ReturnStmtNode,
    "StringLiteral"            : StringLiteralNode,
    "SwitchStmt"               : SwitchStmtNode,
    "TranslationUnitDecl"      : TranslationUnitDeclNode,
    "TypedefDecl"              : TypedefDeclNode,
    "TypedefType"              : TypedefTypeNode,
    "UnaryExprOrTypeTraitExpr" : UnaryExprOrTypeTraitExprNode,
    "UnaryOperator"            : UnaryOperatorNode,
    "UsingDecl"                : UsingDeclNode,
    "UsingShadowDecl"          : UsingShadowDeclNode,
    "VarDecl"                  : VarDeclNode,
    "VisibilityAttr"           : VisibilityAttrNode,
    "WarnUnusedResultAttr"     : WarnUnusedResultAttrNode,
    "WhileStmt"                : WhileStmtNode
}

def getNameById(id):
    return str(AstNode.allNodes[id].name)

def getFileById(id):
    return str(AstNode.allNodes[id].file)

def getNameIdMix(id):
    return str(AstNode.allNodes[id].name) + "." + str(id)

def climbAST():
    r = subprocess.run(["clang", "-Xclang", "-ast-dump=json", srcFilename], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    data = json.loads(r.stdout)
    return nodeKindMap[data["kind"]](data, None)

def buildDependencyGraph():
    dependencyGraph = nx.DiGraph()
    dependencyGraphNamed= nx.DiGraph()

    # Add all the assignments to the graph as edges
    for left, right in VariableAssignment.allAssignments.values():
        if getFileById(left) == srcFilename:
            dependencyGraph.add_edges_from([(r, left) for r in right if r is not None and getFileById(r) == srcFilename])
            dependencyGraphNamed.add_edges_from([(getNameIdMix(r), getNameIdMix(left)) for r in right if r is not None and getFileById(r) == srcFilename])

    # Add all the function calls to the graph as edges
    for funcId, args in FunctionCall.allFuncCalls.values():
        params = FunctionDeclaration.allFuncDeclarations[funcId]
        if len(params) == len(args):
            # TODO: There's bugs with certain functions that have "anonymous" function parameters
            # and malloc() maybe something to do with sizeof() but all other important functions
            # are coming out alright
            for i in range(len(args)):
                if args[i] is not None and getFileById(args[i]) == getFileById(params[i]) == srcFilename:
                    dependencyGraph.add_edge(args[i], params[i])
                    dependencyGraphNamed.add_edge(getNameIdMix(args[i]), getNameIdMix(params[i]))

    # Add all the deep copies from calls of memcpy
    memcpyCalls = [fc for fc in FunctionCall.allFuncCalls.values() if fc[0] == FunctionDeclaration.memcpyId]
    for call in memcpyCalls:
        dst = call[1][0]
        src = call[1][1]
        if dst is not None and src is not None and getFileById(dst) == getFileById(src) == srcFilename:
            dependencyGraph.add_edge(src, dst)
            dependencyGraphNamed.add_edge(getNameIdMix(src), getNameIdMix(dst))

    # Calculate all the nodes that can be reached
    allCopiesSet = nx.shortest_path(dependencyGraph, Variable.varToTraceId).keys()
    allCopiesSetNamed = nx.shortest_path(dependencyGraphNamed, getNameIdMix(Variable.varToTraceId)).keys()
    
    pos = nx.spring_layout(dependencyGraphNamed, seed=1111)
    nx.draw(dependencyGraphNamed, with_labels=True, pos=pos)
    plt.show()

if __name__ == "__main__":
    nodeMap = climbAST()
    buildDependencyGraph()
    