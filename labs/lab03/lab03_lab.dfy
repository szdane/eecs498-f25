// Write a state machine spec representing the factory floor and robot.
datatype Color = Red | Blue

datatype Constants = Constants()
datatype Variables = Variables(factory_stacks: seq<Stack>, robot_stack: Stack, deliveries: nat)


// datatype Disk = Disk(color:Color)
datatype Stack = Stack(items: seq<Color>)
datatype Robot = Robot(counter:int, stack:Stack)
datatype Floor = Floor(stacks: array<Stack>)
// Define any helper predicates/functions as needed.

ghost predicate StackIsALlColor(stack: Stack, color: Color)
{
    forall i: nat | i < |stack.items| :: stack.items[i] == color
}

ghost predicate StackIsALLSameColor(stack:Stack) 
{
    StackIsALlColor(stack, Red) || StackIsALlColor(stack, Blue)
}

ghost predicate Init(c: Constants, v: Variables)
{
    // Fill in here
    && (forall i: nat | i < |v.factory_stacks| :: (|v.factory_stacks[i].items| == 0 || StackIsALLSameColor(v.factory_stacks[i])))
    && (|v.robot_stack.items| == 0 || StackIsALLSameColor(v.robot_stack))
}

ghost predicate PickUp(c: Constants, v: Variables, v': Variables, stack_index: nat)
{
    // Fill in here
    && (stack_index<|v.factory_stacks|)
    && (|v.factory_stacks[stack_index].items|>0)
    && (|v.robot_stack.items| == 0 || v.robot_stack.items[0] == v.factory_stacks[stack_index].items[0])
    && (v'.factory_stacks == v.factory_stacks[stack_index := Stack(v.factory_stacks[stack_index].items[1..])])
    && (v'.robot_stack == Stack([v.factory_stacks[stack_index].items[0]] + v.robot_stack.items))
    && (v'.deliveries == v.deliveries)
}

ghost predicate Drop(c: Constants, v: Variables, v': Variables, stack_index: nat)
{
    // Fill in here
    && (stack_index<|v.factory_stacks|)
    && (|v.robot_stack.items|>0)
    && (|v.factory_stacks[stack_index].items| == 0 || v.robot_stack.items[0] == v.factory_stacks[stack_index].items[0])
}

ghost predicate Deliver(c: Constants, v: Variables, v': Variables)
{
    // Fill in here
    true
}

// Write out the JNF 



ghost predicate Next(c: Constants, v: Variables, v': Variables)
{
    true
}




ghost predicate Safety(c: Constants, v: Variables)
{
    // Fill in the safety condition.
    true
}

// Should prove by itself!
lemma SafetyProof()
    ensures forall c, v :: Init(c, v) ==> Safety(c, v)
    ensures forall c, v, v' :: Safety(c, v) && Next(c, v, v') ==> Safety(c, v')
{
}
