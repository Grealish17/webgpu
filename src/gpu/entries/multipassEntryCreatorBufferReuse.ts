import { workgroupSize } from "../curveSpecific";

/**
 * Creates and executes multipass pipeline. 
 * Assumes that the result buffer of each pass is the input buffer of the next pass.
 * 
 * @param gpu Device to run passes on
 * @param passes Code to run on each pass. Order of list is respected.
 */
export const multipassEntryCreatorReuseBuffers = async (gpu: GPUDevice, passes: IGPUExecution[], entryInfo: IEntryInfo): Promise<Uint32Array> => {
  // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
  const commandEncoder = gpu.createCommandEncoder();

  // Run the passes
  for (let passIndex = 0; passIndex < passes.length; passIndex++) {
    const execution = passes[passIndex];

    const inputData = execution.gpuInput;
    const resultData = execution.gpuOutput;
    const shaderModule = gpu.createShaderModule({ code: execution.shader.code });

    for (let i = 0; i < inputData.inputBuffers.length; i++) {
      const mappedInput = inputData.mappedInputs?.get(i);
      const inputBuffer = inputData.inputBuffers[i];
      if (mappedInput) {
        gpu.queue.writeBuffer(inputBuffer, 0, mappedInput, 0);
      }
    }

    // Create bind group layout
    const bindGroupLayout = createBindGroupLayout(
      gpu,
      inputData.inputBuffers,
      resultData.resultBuffers
    );

    // Create bind group
    const bindGroup = createBindGroup(
      gpu,
      bindGroupLayout,
      inputData.inputBuffers,
      resultData.resultBuffers
    );

    // Create pipeline
    const pipeline = gpu.createComputePipeline({
      layout: gpu.createPipelineLayout({ bindGroupLayouts: [bindGroupLayout] }),
      compute: {
        module: shaderModule,
        entryPoint: execution.shader.entryPoint
      }
    });

    // Run compute pass
    const passEncoder = commandEncoder.beginComputePass();
    passEncoder.setPipeline(pipeline);
    passEncoder.setBindGroup(0, bindGroup);
    passEncoder.dispatchWorkgroups(Math.ceil(entryInfo.numInputs / workgroupSize));
    passEncoder.end();

    // previousResultBuffers = resultBuffers;
  }

  // Create buffer to read result
  const gpuReadBuffer = gpu.createBuffer({
    size: entryInfo.outputSize,
    usage: GPUBufferUsage.COPY_DST | GPUBufferUsage.MAP_READ
  });

  const finalResultBuffer = passes[passes.length - 1].gpuOutput.resultBuffers[0];
  
  // if (previousResultBuffers) {
  commandEncoder.copyBufferToBuffer(
    finalResultBuffer,
    0,
    gpuReadBuffer,
    0,
    entryInfo.outputSize
  );
  // }

  const gpuCommands = commandEncoder.finish();
  gpu.queue.submit([gpuCommands]);

  await gpuReadBuffer.mapAsync(GPUMapMode.READ);
  const arrayBuffer = gpuReadBuffer.getMappedRange();
  const result = new Uint32Array(arrayBuffer.slice(0));
  gpuReadBuffer.unmap();

  return result;
}

/**
 * Description of gpu inputs.
 * 
 * Expected that inputTypes and inputSizes are the same length.
 * mappedInputs should be a map of input index to Uint32Array.
 */
export interface IGPUInput {
  inputBuffers: GPUBuffer[];
  mappedInputs?: Map<number, Uint32Array>;
}

/**
 * Descriptior of gpu result buffers
 * 
 * Expected that resultBufferTypes and resultBufferSizes are the same length.
 */
export interface IGPUResult {
  resultBuffers: GPUBuffer[]
}

export interface IShaderCode {
  code: string;
  entryPoint: string;
}

interface IGPUExecution {
  shader: IShaderCode;
  gpuInput: IGPUInput;
  gpuOutput: IGPUResult;
}

export class GPUExecution implements IGPUExecution {
  shader: IShaderCode;
  gpuInput: IGPUInput;
  gpuOutput: IGPUResult;


  constructor(shader: IShaderCode, gpuInput: IGPUInput, gpuOutput: IGPUResult) {
    this.shader = shader;
    this.gpuInput = gpuInput;
    this.gpuOutput = gpuOutput;
  }
}

export interface IEntryInfo {
  numInputs: number;
  outputSize: number;
}

// Currently has the assumption that input buffers are in order of binding
// Also assumes that the result buffer will always be of type "storage"
const createBindGroupLayout = (device: GPUDevice, gpuInputBuffers: GPUBuffer[], gpuResultBuffers: GPUBuffer[]) => {
  // Bind group layout and bind group
  const layoutEntries: GPUBindGroupLayoutEntry[] = [];
  for (let i = 0; i < gpuInputBuffers.length; i++) {
    layoutEntries.push({
      binding: i,
      visibility: GPUShaderStage.COMPUTE,
      buffer: {
        type: "storage"
      }
    });
  }

  for (let i = 0; i < gpuResultBuffers.length; i++) {
    layoutEntries.push({
      binding: i + gpuInputBuffers.length,
      visibility: GPUShaderStage.COMPUTE,
      buffer: {
        type: "storage"
      }
    });
  }

  const layout = { entries: layoutEntries };

  return device.createBindGroupLayout(layout);
};

const createBindGroup = (device: GPUDevice, bindGroupLayout: GPUBindGroupLayout, gpuInputBuffers: GPUBuffer[], gpuOutputBuffers: GPUBuffer[]) => {
  const inputEntriesToBind = gpuInputBuffers.map((gpuInputBuffer, i) => {
    return {
      binding: i,
      resource: {
        buffer: gpuInputBuffer
      }
    };
  });

  const resultEntriesToBind = gpuOutputBuffers.map((gpuOutputBuffer, i) => {
    return {
      binding: i + gpuInputBuffers.length,
      resource: {
        buffer: gpuOutputBuffer
      }
    }
  });

  const entriesToBind = inputEntriesToBind.concat(resultEntriesToBind);

  const bindGroup = device.createBindGroup({
    layout: bindGroupLayout,
    entries: entriesToBind
  });

  return bindGroup;
};