import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';
import { visualizer } from 'rollup-plugin-visualizer';

declare const process: {
  env: Record<string, string | undefined>;
};

const clientHost = process.env.HOST || 'localhost';
const serverOrigin = process.env.SERVER_ORIGIN || 'http://localhost:5001';
const allowedHosts = ['shine.athergrid.dev'];
const analyzeBundle = process.env.ANALYZE_BUNDLE === '1';

function sourceChunkName(id: string, marker: string, prefix: string) {
  const normalized = id.replace(/\\/g, '/');
  const markerIndex = normalized.indexOf(marker);
  if (markerIndex < 0) return undefined;
  const fileName = normalized.slice(markerIndex + marker.length).split('/')[0]?.replace(/\.[tj]sx?$/, '');
  return fileName ? `${prefix}-${fileName.replace(/[^a-z0-9_-]/gi, '-').toLowerCase()}` : undefined;
}

export default defineConfig({
  plugins: [
    react(),
    ...(analyzeBundle
      ? [visualizer({
        filename: 'dist/bundle-analysis.html',
        template: 'treemap',
        gzipSize: true,
        brotliSize: true,
      })]
      : []),
  ],
  build: {
    rollupOptions: {
      output: {
        manualChunks(id) {
          if (id.includes('node_modules')) {
            if (id.includes('react') || id.includes('@tanstack/react-query')) return 'react';
            if (id.includes('jspdf')) return 'pdf';
            return 'vendor';
          }
          const tabChunk = sourceChunkName(id, '/src/tabs/', 'tab');
          if (tabChunk) return tabChunk;
          const featureChunk = sourceChunkName(id, '/src/features/', 'feature');
          if (featureChunk) return featureChunk;
          if (id.includes('/src/runtime') || id.includes('/src/query')) return 'runtime';
          return undefined;
        },
      },
    },
  },
  server: {
    host: clientHost,
    port: 5000,
    strictPort: true,
    allowedHosts,
    proxy: {
      '/api': {
        target: serverOrigin,
        changeOrigin: true,
      },
      '/auth': {
        target: serverOrigin,
        changeOrigin: true,
      },
    },
  },
  preview: {
    host: clientHost,
    port: 5000,
    strictPort: true,
    allowedHosts,
    proxy: {
      '/api': {
        target: serverOrigin,
        changeOrigin: true,
      },
      '/auth': {
        target: serverOrigin,
        changeOrigin: true,
      },
    },
  },
});
