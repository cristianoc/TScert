export interface ServiceHandle {
  readonly id: string;
  ping(): boolean;
}

export declare class ServiceHandleImpl implements ServiceHandle {
  readonly id: string;
  constructor(id: string);
  ping(): boolean;
}

export declare const ServiceHandle: typeof ServiceHandleImpl;

export declare function openHandle(): ServiceHandle;

export interface BadNamespaceMerge {
  readonly x: number;
}

export declare namespace BadNamespaceMerge {
  export const y: number;
}
