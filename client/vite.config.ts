import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';

export default defineConfig({
  plugins: [react()],
  build: {
    rollupOptions: {
      output: {
        manualChunks: {
          react: ['react', 'react-dom'],
        },
      },
    },
  },
  server: {
    host: '::1',
    port: 5000,
    strictPort: true,
    allowedHosts: ['shine.athergrid.dev'],
    proxy: {
      '/api': {
        target: 'http://[::1]:5001',
        changeOrigin: true,
      },
      '/auth': {
        target: 'http://[::1]:5001',
        changeOrigin: true,
      },
    },
  },
  preview: {
    host: '::1',
    port: 5000,
    strictPort: true,
    allowedHosts: ['shine.athergrid.dev'],
    proxy: {
      '/api': {
        target: 'http://[::1]:5001',
        changeOrigin: true,
      },
      '/auth': {
        target: 'http://[::1]:5001',
        changeOrigin: true,
      },
    },
  },
});
