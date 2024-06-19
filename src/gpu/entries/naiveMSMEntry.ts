import { CurveWGSL } from "../wgsl/Curve";
import { FieldModulusWGSL } from "../wgsl/FieldModulus";
import { CurveType, getCurveBaseFunctionsWGSL, getCurveParamsWGSL, sumExtPoints, workgroupSize } from "../curveSpecific";
import { gpuU32Inputs, u32ArrayToBigInts } from "../utils";
import { IEntryInfo, IGPUInput, IGPUResult, IShaderCode, multipassEntryCreator } from "./multipassEntryCreator";
import { GPUExecution } from "./multipassEntryCreator";
import { U256WGSL } from "../wgsl/U256";
import { AFFINE_POINT_SIZE, EXT_POINT_SIZE, FIELD_SIZE } from "../U32Sizes";
import { prune } from "../prune";

export const naive_msm = async (
  input1: gpuU32Inputs,
  input2: gpuU32Inputs,
  curve: CurveType
  ) => {
  const [execution, entryInfo] = point_mul_multipass_info(input1, input2, curve);

  const bufferResult = await multipassEntryCreator(execution, entryInfo);
  //const bigIntResult = u32ArrayToBigInts(bufferResult || new Uint32Array(0));

  //return sumExtPoints(curve, bigIntResult);
  return bufferResult;
}

export const point_mul_multipass_info = (
  affinePoints: gpuU32Inputs,
  scalars: gpuU32Inputs,
  curve: CurveType
): [GPUExecution[], IEntryInfo] => {
  const numInputs = affinePoints.u32Inputs.length / affinePoints.individualInputSize;
  const baseModules = [
    U256WGSL,
    getCurveParamsWGSL(curve),
    FieldModulusWGSL,
    getCurveBaseFunctionsWGSL(curve),
    CurveWGSL
  ];

  const affinePointsBufferSize = Uint32Array.BYTES_PER_ELEMENT * numInputs * AFFINE_POINT_SIZE; // 2 fields per affine point
  const scalarsBufferSize = Uint32Array.BYTES_PER_ELEMENT * numInputs * FIELD_SIZE;
  const pointsBufferSize = Uint32Array.BYTES_PER_ELEMENT * numInputs * EXT_POINT_SIZE; // 4 fields per point

  const batchAffineTrickEntry = `
  @group(0) @binding(0)
  var<storage, read> affine_points: array<AffinePoint>;
  @group(0) @binding(1)
  var<storage, read> scalars: array<Field>;
  @group(0) @binding(2)
  var<storage, read_write> points: array<array<AffinePoint, 1000>, 256>;
  @group(0) @binding(3)
  var<storage, read_write> scratch_space: array<array<AffinePoint, 500>, 256>;
  @group(0) @binding(4)
  var<storage, read_write> nums: array<i32, 256>;
  @group(0) @binding(5)
  var<storage, read_write> output: array<AffinePoint>;

  @compute @workgroup_size(${workgroupSize})
  fn main(
    @builtin(global_invocation_id) global_id : vec3<u32>
  ) {
    var len = u32(arrayLength(&affine_points));
    var bit_num = global_id.x;

    for (var i = 0u; i < 1000u; i++) {
      var p = affine_points[i];
      var s = scalars[i];
      if (get_bit(s, bit_num) == u32(1)) {
        points[bit_num][nums[bit_num]] = p;
        nums[bit_num]++;
      }
    }

    var n = nums[bit_num];
    // var n = 2;
    while (n > 1) {
      var batch = U256_ONE;
      for (var i = 0; i < n; i+=2) {
        scratch_space[bit_num][i >> 1].x = field_add(points[bit_num][i].x, points[bit_num][i + 1].x);   // x2 + x1
        points[bit_num][i + 1].x = field_sub(points[bit_num][i + 1].x, points[bit_num][i].x);           // x2 - x1
        points[bit_num][i + 1].y = field_sub(points[bit_num][i + 1].y, points[bit_num][i].y);           // y2 - y1
        points[bit_num][i + 1].y = field_multiply(points[bit_num][i + 1].y, batch);                     // (y2 - y1)*accumulator_old
        batch = field_multiply(batch, points[bit_num][i + 1].x); 
      }
      
      //batch = inverse(batch);
      

      for (var i = n-2; i >= 0; i-=2) {
        points[bit_num][i + 1].y = field_multiply(points[bit_num][i + 1].y, batch);                                // update accumulator
        batch = field_multiply(batch, points[bit_num][i + 1].x);
        points[bit_num][i + 1].x = field_multiply(points[bit_num][i + 1].y, points[bit_num][i + 1].y);             // lambda_sqr
        scratch_space[bit_num][i >> 1].x = field_sub(points[bit_num][i + 1].x, scratch_space[bit_num][i >> 1].x);  // lambda_sqr - x2 - x1

        points[bit_num][i].x = field_sub(points[bit_num][i].x, scratch_space[bit_num][i >> 1].x);
        points[bit_num][i].x = field_multiply(points[bit_num][i].x, points[bit_num][i + 1].y);
        scratch_space[bit_num][i >> 1].y = field_sub(points[bit_num][i].x, points[bit_num][i].y);
      }
      

      for (var i = 0; i < n/2; i++) {
        points[bit_num][i] = scratch_space[bit_num][i];
      }

      n = (n+1)/2;
    }
    
    output[bit_num] = points[bit_num][0];    
  }
`;

  const calcExtendedPointsEntry = `
    @group(0) @binding(0)
    var<storage, read> input: array<AffinePoint>;
    @group(0) @binding(1)
    var<storage, read> scalars: array<Field>;
    @group(0) @binding(2)
    var<storage, read_write> output: array<Point>;

    @compute @workgroup_size(${workgroupSize})
    fn main(
      @builtin(global_invocation_id) global_id : vec3<u32>
    ) {
      var p1 = input[global_id.x];
      var p1_t = field_multiply(p1.x, p1.y);
      var z = U256_ONE;
      var ext_p1 = Point(p1.x, p1.y, p1_t, z);

      output[global_id.x] = ext_p1;
    }
  `;

  const executionSteps: GPUExecution[] = [];

  const batchAffineTrickShaderCode = prune(
    baseModules.join(''),
    ['get_bit', 'inverse', 'field_multiply', 'field_sub', 'field_add']
  ) + batchAffineTrickEntry;

  const batchAffineTrickShader: IShaderCode = {
    code: batchAffineTrickShaderCode,
    entryPoint: "main"
  }

  const batchAffineTrickInputs: IGPUInput = {
    inputBufferTypes: ["read-only-storage", "read-only-storage", "storage", "storage", "storage"],
    inputBufferSizes: [affinePointsBufferSize, scalarsBufferSize, affinePointsBufferSize*256, scalarsBufferSize*256, 4*256],
    inputBufferUsages: [GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC],
    mappedInputs: new Map<number, Uint32Array>([[0, affinePoints.u32Inputs], [1, scalars.u32Inputs]])
  }

  const batchAffineTrickResult: IGPUResult = {
    resultBufferTypes: ["storage"],
    resultBufferSizes: [4*256*16],
    resultBufferUsages: [GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC]
  }

  const batchAffineTrickStep = new GPUExecution(batchAffineTrickShader, batchAffineTrickInputs, batchAffineTrickResult);
  executionSteps.push(batchAffineTrickStep);

  const calcExtendedPointsShaderCode = prune(
    baseModules.join(''),
    ['field_multiply']
  ) + calcExtendedPointsEntry;

  const calcExtendedPointsShader: IShaderCode = {
    code: calcExtendedPointsShaderCode,
    entryPoint: "main"
  }

  const calcExtendedPointsInputs: IGPUInput = {
    inputBufferTypes: ["read-only-storage", "read-only-storage"],
    inputBufferSizes: [4*256*16, scalarsBufferSize],
    inputBufferUsages: [GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST],
    //mappedInputs: new Map<number, Uint32Array>([[0, affinePoints.u32Inputs], [1, scalars.u32Inputs]])
  }

  const calcExtendedPointsResult: IGPUResult = {
    resultBufferTypes: ["storage"],
    resultBufferSizes: [4*256*32],
    resultBufferUsages: [GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC]
  }

  const calcExtendedPointsStep = new GPUExecution(calcExtendedPointsShader, calcExtendedPointsInputs, calcExtendedPointsResult);
  executionSteps.push(calcExtendedPointsStep);

  const entryInfo: IEntryInfo = {
    numInputs: numInputs,
    outputSize: 4*256*32
  }

  return [executionSteps, entryInfo];
}

export const point_mul_multipass_inf = (
  affinePoints: gpuU32Inputs,
  scalars: gpuU32Inputs,
  curve: CurveType
): [GPUExecution[], IEntryInfo] => {
  const numInputs = affinePoints.u32Inputs.length / affinePoints.individualInputSize;
  const baseModules = [
    U256WGSL,
    getCurveParamsWGSL(curve),
    FieldModulusWGSL,
    getCurveBaseFunctionsWGSL(curve),
    CurveWGSL
  ];
  const affinePointsBufferSize = Uint32Array.BYTES_PER_ELEMENT * numInputs * AFFINE_POINT_SIZE; // 2 fields per affine point
  const scalarsBufferSize = Uint32Array.BYTES_PER_ELEMENT * numInputs * FIELD_SIZE;
  const pointsBufferSize = Uint32Array.BYTES_PER_ELEMENT * numInputs * EXT_POINT_SIZE; // 4 fields per point

  const calcExtendedPointsEntry = `
    @group(0) @binding(0)
    var<storage, read> input1: array<AffinePoint>;
    @group(0) @binding(1)
    var<storage, read_write> output: array<Point>;

    @compute @workgroup_size(${workgroupSize})
    fn main(
      @builtin(global_invocation_id) global_id : vec3<u32>
    ) {
      var p1 = input1[global_id.x];
      var p1_t = field_multiply(p1.x, p1.y);
      var z = U256_ONE;
      var ext_p1 = Point(p1.x, p1.y, p1_t, z);

      output[global_id.x] = ext_p1;
    }
  `;

  const mulPointFirstStepEntry = `
    @group(0) @binding(0)
    var<storage, read> points: array<Point>;
    @group(0) @binding(1)
    var<storage, read> scalars: array<Field>;
    @group(0) @binding(2)
    var<storage, read_write> output: array<Point>;
    @group(0) @binding(3)
    var<storage, read_write> updatedScalars: array<Field>;
    @group(0) @binding(4)
    var<storage, read_write> newTemps: array<Point>;

    @compute @workgroup_size(${workgroupSize})
    fn main(
      @builtin(global_invocation_id) global_id : vec3<u32>
    ) {
      var point = points[global_id.x];
      var scalar = scalars[global_id.x];

      var multiplied = mul_point_64_bits_start(point, scalar);
      output[global_id.x] = multiplied.result;
      updatedScalars[global_id.x] = multiplied.scalar;
      newTemps[global_id.x] = multiplied.temp;
    }
  `;

  const mulPointIntermediateStepEntry = `
    @group(0) @binding(0)
    var<storage, read> points: array<Point>;
    @group(0) @binding(1)
    var<storage, read> scalars: array<Field>;
    @group(0) @binding(2)
    var<storage, read> prevTemps: array<Point>;
    @group(0) @binding(3)
    var<storage, read_write> output: array<Point>;
    @group(0) @binding(4)
    var<storage, read_write> updatedScalars: array<Field>;
    @group(0) @binding(5)
    var<storage, read_write> newTemps: array<Point>;

    @compute @workgroup_size(${workgroupSize})
    fn main(
      @builtin(global_invocation_id) global_id : vec3<u32>
    ) {
      var point = points[global_id.x];
      var scalar = scalars[global_id.x];
      var temp = prevTemps[global_id.x];
      var multipliedIntermediate = mul_point_64_bits(point, scalar, temp);
      output[global_id.x] = multipliedIntermediate.result;
      updatedScalars[global_id.x] = multipliedIntermediate.scalar;
      newTemps[global_id.x] = multipliedIntermediate.temp;
    }
  `;

  const mulPointFinalStepEntry = `
    @group(0) @binding(0)
    var<storage, read> points: array<Point>;
    @group(0) @binding(1)
    var<storage, read> scalars: array<Field>;
    @group(0) @binding(2)
    var<storage, read> prevTemps: array<Point>;
    @group(0) @binding(3)
    var<storage, read_write> output: array<Point>;

    @compute @workgroup_size(${workgroupSize})
    fn main(
      @builtin(global_invocation_id) global_id : vec3<u32>
    ) {
      var point = points[global_id.x];
      var scalar = scalars[global_id.x];
      var temp = prevTemps[global_id.x];
      var multiplied = mul_point_64_bits(point, scalar, temp);
      output[global_id.x] = multiplied.result;
    }
  `;

  const executionSteps: GPUExecution[] = [];

  // Step 1: Calculate extended points
  const calcExtendedPointsShaderCode = prune(
    baseModules.join(''),
    ['field_multiply']
  ) + calcExtendedPointsEntry;
  const calcExtendedPointsShader: IShaderCode = {
    code: calcExtendedPointsShaderCode,
    entryPoint: "main"
  }
  const calcExtendedPointsInputs: IGPUInput = {
    inputBufferTypes: ["read-only-storage"],
    inputBufferSizes: [affinePointsBufferSize],
    inputBufferUsages: [GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST],
    mappedInputs: new Map<number, Uint32Array>([[0, affinePoints.u32Inputs]])
  }
  const calcExtendedPointsResult: IGPUResult = {
    resultBufferTypes: ["storage"],
    resultBufferSizes: [pointsBufferSize],
    resultBufferUsages: [GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC]
  }
  const calcExtendedPointsStep = new GPUExecution(calcExtendedPointsShader, calcExtendedPointsInputs, calcExtendedPointsResult);
  executionSteps.push(calcExtendedPointsStep);

  // Step 2: Multiply points by scalars
  const mulPointFirstStepEntryShaderCode = prune(
    baseModules.join(''),
    ['mul_point_64_bits_start']
  ) + mulPointFirstStepEntry;
  const firstMulPointShader: IShaderCode = {
    code: mulPointFirstStepEntryShaderCode,
    entryPoint: "main"
  }
  const firstMulPointInputs: IGPUInput = {
    inputBufferTypes: ["read-only-storage", "read-only-storage"],
    inputBufferSizes: [pointsBufferSize, scalarsBufferSize],
    inputBufferUsages: [GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST],
    mappedInputs: new Map<number, Uint32Array>([[1, scalars.u32Inputs]])
  }
  const firstMulPointOutputs: IGPUResult = {
    resultBufferTypes: ["storage", "storage", "storage"],
    resultBufferSizes: [pointsBufferSize, scalarsBufferSize, pointsBufferSize],
    resultBufferUsages: [GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC]
  }
  const firstMulPointStep = new GPUExecution(firstMulPointShader, firstMulPointInputs, firstMulPointOutputs);
  executionSteps.push(firstMulPointStep);
  for (let i = 0; i < 2; i++) {
    const mulPointIntermediateStepEntryShaderCode = prune(
      baseModules.join(''),
      ['mul_point_64_bits']
    ) + mulPointIntermediateStepEntry;
    const multPointShader: IShaderCode = {
      code: mulPointIntermediateStepEntryShaderCode,
      entryPoint: "main"
    }
    const mulPointInputs: IGPUInput = {
      inputBufferTypes: ["read-only-storage", "read-only-storage", "read-only-storage"],
      inputBufferSizes: [pointsBufferSize, scalarsBufferSize, pointsBufferSize],
      inputBufferUsages: [GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST]
    }
    const mulPointResult: IGPUResult = {
      resultBufferTypes: ["storage", "storage", "storage"],
      resultBufferSizes: [pointsBufferSize, scalarsBufferSize, pointsBufferSize],
      resultBufferUsages: [GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC]
    }
    const mulPointStep = new GPUExecution(multPointShader, mulPointInputs, mulPointResult);
    executionSteps.push(mulPointStep);
  }
  const mulPointFinalStepShaderCode = prune(
    baseModules.join(''),
    ['mul_point_64_bits']
  ) + mulPointFinalStepEntry;
  const finalMultPointShader: IShaderCode = {
    code: mulPointFinalStepShaderCode,
    entryPoint: "main"
  }
  const finalMulPointInputs: IGPUInput = {
    inputBufferTypes: ["read-only-storage", "read-only-storage", "read-only-storage"],
    inputBufferSizes: [pointsBufferSize, scalarsBufferSize, pointsBufferSize],
    inputBufferUsages: [GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST]
  }
  const finalMulPointResult: IGPUResult = {
    resultBufferTypes: ["storage"],
    resultBufferSizes: [pointsBufferSize],
    resultBufferUsages: [GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC]
  }
  const finalMulPointStep = new GPUExecution(finalMultPointShader, finalMulPointInputs, finalMulPointResult);
  executionSteps.push(finalMulPointStep);

  const entryInfo: IEntryInfo = {
    numInputs: numInputs,
    outputSize: pointsBufferSize
  }

  return [executionSteps, entryInfo];
}

// eslint-disable-next-line @typescript-eslint/no-explicit-any
(window as any).naive_msm = naive_msm;